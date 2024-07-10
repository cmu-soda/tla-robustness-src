package recomp;

import java.util.List;

public class RVStrategy implements Runnable {
    public static boolean globalIsDone = false;

    private String tla;
    private String cfg;
    private String recompType;
    private String recompFile;
    private boolean verbose;

    public RVStrategy(String tla, String cfg, String recompType, String recompFile, boolean verbose) throws InterruptedException {
        this.tla = tla;
        this.cfg = cfg;
        this.recompType = recompType;
        this.recompFile = recompFile;
        this.verbose = verbose;
    }

    synchronized static public boolean isThreadDone() {
        boolean isDone = globalIsDone;
        globalIsDone = true;
        return isDone;
    }

    public static void runRVStrategies(String tla, String cfg, String recompType, String recompFile, boolean verbose) throws InterruptedException {
//		ArrayList<Thread> threads = new ArrayList<>();
        RVStrategy sampleStrategy = new RVStrategy(tla, cfg, recompType, recompFile, verbose);
        Thread thread = new Thread(sampleStrategy);
        thread.start();

        try {
            thread.join();
        } catch (InterruptedException e) {
            System.out.println("Thread interrupted while waiting on something.");
        }
        System.exit(99);
    }

    @ Override
    public void run() {
        try {
            List<String> rawComponents = Decomposition.decompAll(tla, cfg);
            RecompVerify.runRecompMap(tla, cfg, recompType, recompFile, verbose, rawComponents);
        } catch (Exception e) {
            System.out.println("Thread interrupted while waiting on something.");
        }
    }
}
