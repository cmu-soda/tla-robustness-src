import concurrent.futures
import glob
import os
import shutil
import subprocess
import sys
from functools import partial

root_dir = os.path.dirname(os.path.abspath(__file__))
tool = root_dir + "/bin/recomp-verify.jar"
tlc = root_dir + "/bin/tla2tools.jar"

def write(name, contents):
    with open(name, "w") as f:
        f.write(contents)

def decomp(spec, cfg):
    cmd_args = ["java", "-jar", tool, spec, cfg, "--decomp"]
    ret = subprocess.run(cmd_args, capture_output=True, text=True)
    return ret.stdout.rstrip().split(",")

def create_err_trace(txt):
    lines = txt.split("\n")
    keep = []
    capture = False
    for l in lines:
        if "Error:" in l:
            capture = True
        if "distinct states found" in l:
            capture = False
        if capture and "errCounter" not in l:
            keep.append(l)
    return "\n".join(keep)

def verify(spec, cfg, cust, naive, verbose):
    # run model checking alg
    # use subprocess.call to send the output to stdout
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
    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"


    #shutil.copyfile(spec, "out/"+spec)
    #shutil.copyfile(cfg, "out/"+cfg)
    for filename in glob.glob(os.path.join(orig_dir, '*.*')):
        shutil.copy(filename, dest_dir)

    os.chdir("out")
    verify(spec, cfg, cust, naive, verbose)
    os.chdir(orig_dir)

def verify_capture_output(spec, cfg, pdir, *args):
    shutil.copy(spec, pdir + "/")
    shutil.copy(cfg, pdir + "/")
    #os.chdir(pdir)
    #write("out.log","")

    cmd_args = ["java", "-Xmx7g", "-jar", tool, spec, cfg]
    for arg in args:
        cmd_args.append(arg)

    # uses TLC to run the one-component case
    if pdir == "mono":
        cmd_args = ["java", "-Xmx7g", "-jar", tlc, "-deadlock", "-workers", "1", "-config", cfg, spec]
   
    #naive_log = open("out.log","w")
    #process = subprocess.Popen(cmd_args, stdout=naive_log.fileno())
    #process.wait()
    #return open("naive/out.log").read().rstrip()
    #ret = subprocess.run(cmd_args, capture_output=True, text=True)
    
    cd_args = ["cd", pdir]
    cmd = " ".join(cd_args) + "; " + " ".join(cmd_args)
    ret = subprocess.run(cmd, capture_output=True, text=True, shell=True)

    return ret.stdout.rstrip()

def run_multi_verif(dest_dir, spec, cfg, halt=False):
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=8)
    futures = []
    
    # spawn a process for the naive map
    f = partial(verify_capture_output, spec, cfg, "naive", "--naive")
    futures.append(executor.submit(f))
    
    # spawn a process for each recomp map
    pdirs = ["mono", "cust_1", "cust_2"]
    for pdir in pdirs:
        f = partial(verify_capture_output, spec, cfg, pdir, "--cust", "custom_recomp.csv")
        futures.append(executor.submit(f))
    
    done, not_done = concurrent.futures.wait(futures, return_when=concurrent.futures.FIRST_COMPLETED if halt else concurrent.futures.ALL_COMPLETED)

    # we cancel the ones that have not finished
    if halt:
        for future in not_done:
            future.cancel()

    winner = done.pop()
    output = winner.result()
    #for future in not_done:
        #future.cancel()
    return output

def verify_multi_process(spec, cfg, verbose, halt=False):
    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"
    shutil.copy(spec, dest_dir)
    shutil.copy(cfg, dest_dir)
    os.chdir("out")

    os.makedirs("decomp", exist_ok=True)
    shutil.copy(spec, "decomp/")
    shutil.copy(cfg, "decomp/")
    os.chdir("decomp")
    components = decomp(spec, cfg)
    os.chdir(dest_dir)

    # if there's only one component then there is no need to run multiple processes
    if len(components) <= 1:
        #os.chdir(orig_dir)
        #verify_single_process(spec, cfg, False, False, verbose)
        os.makedirs("mono", exist_ok=True)
        output = verify_capture_output(spec, cfg, "mono")
        print(output)
        return

    # otherwise, build three recomp maps
    os.makedirs("mono", exist_ok=True)
    os.makedirs("cust_1", exist_ok=True)
    os.makedirs("cust_2", exist_ok=True)
    mono = ",".join(components) + "\n"
    recomp_1 = components[0] + "\n" + ",".join(components[1:]) + "\n"
    recomp_2 = ",".join(components[0:-1]) + "\n" + components[-1] + "\n"
    write("mono/custom_recomp.csv", mono)
    write("cust_1/custom_recomp.csv", recomp_1)
    write("cust_2/custom_recomp.csv", recomp_2)

    os.makedirs("naive", exist_ok=True)

    output = run_multi_verif(dest_dir, spec, cfg, halt=halt)
    print(output)

def run():
    if len(sys.argv) < 3 or len(sys.argv) > 6:
        print("usage: recomp-verify.py <file.tla> <file.cfg> [--cust|--naive|--parallel|--halt] [--verbose]")
        return

    spec = sys.argv[1]
    cfg = sys.argv[2]
    multi_process = "--parallel" in sys.argv
    cust = "--cust" in sys.argv
    naive = "--naive" in sys.argv
    verbose = "--verbose" in sys.argv
    halt = "--halt" in sys.argv

    if multi_process:
        verify_multi_process(spec, cfg, verbose, halt=halt)
    else:
        verify_single_process(spec, cfg, cust, naive, verbose)

run()
