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
    
    print("Command to run:", cmd_args)  # Confirm the command with --cust
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
    # Get the absolute path to recomp-verify.py using root_dir
    script_path = os.path.join(root_dir, "recomp-verify.py")

    # Prepare the individual subdirectories for each verification case
    subdirs = ["mono", "cust_1", "cust_2", "naive"]
    
    # Prepare the individual commands for each verification directory
    # cfg = os.path.abspath(cfg)
    # spec = os.path.abspath(spec)
    no_invs_cfg = os.path.abspath(os.path.join(os.path.dirname(cfg), "no_invs.cfg"))  # Get absolute path to no_invs.cfg
    print(no_invs_cfg)

    # Loop through subdirs to create each directory and copy spec, cfg, and no_invs.cfg files
    for subdir in subdirs:
        subdir_path = os.path.join(dest_dir, subdir)
        os.makedirs(subdir_path, exist_ok=True)

        # Copy the .tla, .cfg, and no_invs.cfg files into each subdirectory
        shutil.copy(spec, subdir_path)
        shutil.copy(cfg, subdir_path)
        shutil.copy(no_invs_cfg, subdir_path)

    # Construct parallel command as before
    print(script_path)
    print(spec)
    print(cfg)
    
    parallel_cmds = [
        f'"cd {os.path.join(dest_dir, "mono")} && python3 {script_path} {spec} {cfg} --cust"'
        f'cd {os.path.join(dest_dir, "cust_1")} && python3 {script_path} {spec} {cfg} --cust',
        f'cd {os.path.join(dest_dir, "cust_2")} && python3 {script_path} {spec} {cfg} --cust',
        f'cd {os.path.join(dest_dir, "naive")} && python3 {script_path} {spec} {cfg} --naive'
    ]

    for i in range(len(parallel_cmds)):
        print(i, " : ", parallel_cmds[i])


    
    # Use parallel with --halt and other options
    parallel_cmd = f"parallel --halt now,success=1 --line-buffer --keep-order ::: {' '.join(parallel_cmds)}"

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
    shutil.copy("no_invs.cfg", dest_dir + "/no_invs.cfg")

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
    multi_process = "--parallel" in sys.argv
    cust = "--cust" in sys.argv
    naive = "--naive" in sys.argv
    verbose = "--verbose" in sys.argv
    print("Cust is: " , cust)

    if multi_process:
        verify_multi_process(spec, cfg, verbose)
    else:
        verify_single_process(spec, cfg, cust, naive, verbose)

run()

# Force exit to avoid zombie processes in certain cases
os._exit(0)