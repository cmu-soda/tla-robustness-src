import glob
import shlex
import os
import shutil
import subprocess
import sys
from functools import partial

root_dir = os.path.dirname(os.path.abspath(__file__))
tool = root_dir + "/bin/recomp-verify.jar"
tlc = root_dir + "/bin/tla2tools.jar"

def write(name, contents):
    # Writes contents to a file
    with open(name, "w") as f:
        f.write(contents)

def decomp(spec, cfg):
    # Decomposes the spec and cfg using the recomp tool
    cmd_args = ["java", "-jar", tool, spec, cfg, "--decomp"]
    ret = subprocess.run(cmd_args, capture_output=True, text=True)
    return ret.stdout.rstrip().split(",")

def create_err_trace(txt):
    # Extracts error trace from the model checking output
    lines = txt.split("\n")
    keep = []
    capture = False
    for l in lines:
        if ("Error:" in l):
            capture = True
        if ("distinct states found" in l):
            capture = False
        if (capture and "errCounter" not in l):
            keep.append(l)
    return "\n".join(keep)

def verify(spec, cfg, cust, naive, verbose):
    # Runs the model checking algorithm
    # Use subprocess.call to send the output to stdout
    cmd_args = ["java", "-Xmx25g", "-jar", tool, spec, cfg]
    if cust:
        cmd_args.append("--cust")
        cmd_args.append("custom_recomp.csv")
    if naive:
        cmd_args.append("--naive")
    if verbose:
        cmd_args.append("--verbose")
    retcode = subprocess.call(cmd_args)

    if retcode == 99:
        replay_args = ["java", "-jar", tlc, "-deadlock", "ErrTrace.tla"]
        replay = subprocess.run(replay_args, capture_output=True, text=True)
        replay_out = replay.stdout
        if "Error:" in replay_out:
            err_trace = create_err_trace(replay_out)
            print("Here is the error trace:\n")
            print(err_trace)
        else:
            print("Could not confirm the violating trace in the TLA+ spec; this is a bug in the tool.")

def verify_single_process(spec, cfg, cust, naive, verbose):
    # Sets up directories and copies necessary files for single-process verification
    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"

    for filename in glob.glob(os.path.join(orig_dir, '*.*')):
        shutil.copy(filename, dest_dir)

    os.chdir("out")
    verify(spec, cfg, cust, naive, verbose)
    os.chdir(orig_dir)

def verify_capture_output(spec, cfg, pdir, *args):
    # Captures output of the verification process
    shutil.copy(spec, pdir + "/")
    shutil.copy(cfg, pdir + "/")

    cmd_args = ["java", "-Xmx7g", "-jar", tool, spec, cfg]
    for arg in args:
        cmd_args.append(arg)

    # Uses TLC to run the one-component case
    if pdir == "mono":
        cmd_args = ["java", "-Xmx7g", "-jar", tlc, "-deadlock", "-workers", "1", "-config", cfg, spec]

    cd_args = ["cd", pdir]
    cmd = " ".join(cd_args) + "; " + " ".join(cmd_args)
    ret = subprocess.run(cmd, capture_output=True, text=True, shell=True)

    return ret.stdout.rstrip()

def run_multi_verif_with_parallel(dest_dir, spec, cfg):
    # Prepare the individual commands for each verification directory
    pdirs = ["mono", "cust_1", "cust_2", "naive"]
    
    # Create the parallel commands list
    parallel_cmds = []
    for pdir in pdirs:
        if pdir == "naive":
            cmd = f"java -Xmx7g -jar {shlex.quote(tool)} {shlex.quote(spec)} {shlex.quote(cfg)} --naive"
        else:
            cmd = f"java -Xmx7g -jar {shlex.quote(tool)} {shlex.quote(spec)} {shlex.quote(cfg)} --cust custom_recomp.csv"
        
        # Append the command, wrapped in quotes, to the list
        parallel_cmds.append(shlex.quote(cmd))
    
    # Use parallel with --halt and other options
    parallel_cmd = f"parallel --halt now,fail=1 --line-buffer --keep-order ::: {' '.join(parallel_cmds)}"

    # Run the parallel command
    process = subprocess.Popen(parallel_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True, text=True)

    # Print the output in real-time
    for line in process.stdout:
        print(line, end="")

    # Wait for the process to finish
    process.wait()

    # If there's an error, print the stderr output
    if process.returncode != 0:
        print(process.stderr.read())  # Display error output


def verify_multi_process(spec, cfg, verbose):
    # Sets up directories and runs multi-process verification using the 'parallel' command
    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"
    shutil.copy(spec, dest_dir)
    shutil.copy(cfg, dest_dir)
    os.chdir("out")

    # Decompose the spec and cfg
    os.makedirs("decomp", exist_ok=True)
    shutil.copy(spec, "decomp/")
    shutil.copy(cfg, "decomp/")
    os.chdir("decomp")
    components = decomp(spec, cfg)
    os.chdir(dest_dir)

    # If there's only one component, there is no need to run multiple processes
    if len(components) <= 1:
        os.makedirs("mono", exist_ok=True)
        output = verify_capture_output(spec, cfg, "mono")
        print(output)
        return

    # Otherwise, build three recomp maps
    os.makedirs("mono", exist_ok=True)
    os.makedirs("cust_1", exist_ok=True)
    os.makedirs("cust_2", exist_ok=True)
    mono = ",".join(components) + "\n"
    recomp_1 = components[0] + "\n" + ",".join(components[1:]) + "\n"
    recomp_2 = ",".join(components[0:-1]) + "\n" + components[-1] + "\n"
    write("mono/custom_recomp.csv", mono)
    write("cust_1/custom_recomp.csv", recomp_1)
    write("cust_2/custom_recomp.csv", recomp_2)

    # Also run the naive mapping
    os.makedirs("naive", exist_ok=True)

    # Run the verification processes in parallel
    output = run_multi_verif_with_parallel(dest_dir, spec, cfg)
    print(output)

def run():
    # Parse arguments and run the appropriate verification process
    if len(sys.argv) < 3 or len(sys.argv) > 5:
        print("usage: recomp-verify.py <file.tla> <file.cfg> [--cust|--naive|--parallel] [--verbose]")
        return

    spec = sys.argv[1]
    cfg = sys.argv[2]
    multi_process = len(sys.argv) >= 4 and sys.argv[3] == "--parallel"
    cust = (len(sys.argv) >= 4 and sys.argv[3] == "--cust") or (len(sys.argv) >= 5 and sys.argv[4] == "--cust")
    naive = (len(sys.argv) >= 4 and sys.argv[3] == "--naive") or (len(sys.argv) >= 5 and sys.argv[4] == "--naive")
    verbose = (len(sys.argv) >= 4 and sys.argv[3] == "--verbose") or (len(sys.argv) >= 5 and sys.argv[4] == "--verbose")

    if multi_process:
        verify_multi_process(spec, cfg, verbose)
    else:
        verify_single_process(spec, cfg, cust, naive, verbose)

run()

# Force exit to avoid zombie processes in certain cases
os._exit(0)
