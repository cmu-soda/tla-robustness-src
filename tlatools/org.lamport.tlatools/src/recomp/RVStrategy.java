package recomp;

import cmu.isr.ts.LTS;
import cmu.isr.ts.ParallelComposition;
import cmu.isr.ts.lts.SafetyUtils;
import lts.SymbolTable;
import tlc2.AlphabetMembershipTester;
import tlc2.TLC;
import tlc2.Utils;

import java.util.ArrayList;
import java.util.List;

import static recomp.RecompVerify.writeErrorTraceFile;

public class RVStrategy implements Runnable {
    /**
     * Implements a specific recomposition strategy on its own thread. After decomposing a TLA file
     * into components, it uses the instatiated recomposition Strategy to model check.
     *
     * Multiple RVStragegy instances are meant to be run in parallel (check RecompVerify.java)
     **/

    // Global variable for purpose of seeing when threads are done
    public static String globalPrintMsg = null;

    private String tla;
    private String cfg;
    private String recompType;
    private String recompFile;
    private boolean verbose;
    private RVResult result;


    public RVStrategy(String tla, String cfg, String recompType, String recompFile, boolean verbose, RVResult result) throws InterruptedException {
        this.tla = tla;
        this.cfg = cfg;
        this.recompType = recompType;
        this.recompFile = recompFile;
        this.verbose = verbose;
        this.result = result;
    }

    // Each thread needs a run() method
    @ Override
    public void run() {
        // Each tread performs runRecompStrategy with the given instance variables of the instantiated class
        try {
            List<String> rawComponents = Decomposition.decompAll(tla, cfg);
            runRecompStrategy(rawComponents);
        } catch (Exception e) {
            System.out.println("Thread interrupted while waiting on something.");
        }
    }

    // runs a singular recompositionStrategy (from the choices of bottom-heavy, top-heavy, identity, etc.
    public void runRecompStrategy(final List<String> rawComponents) {
        String printMsg = "";
        PerfTimer timer = new PerfTimer();
        SymbolTable.init();

        final String noInvsCfg = "no_invs.cfg";

        // decompose the spec into as many components as possible
        final List<String> components = Composition.symbolicCompose(tla, cfg, recompType, recompFile, rawComponents);
        Utils.assertTrue(rawComponents.size() > 0, "Decomposition returned no components");
        Utils.assertTrue(components.size() > 0, "Symbolic composition returned no components");
        printMsg = Utils.addPrint(printMsg, "n: " + rawComponents.size());
        printMsg = Utils.addPrint(printMsg, ("m: " + (components.size() - 1)));

        // model check the first component
        final String firstComp = components.get(0);
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "Component 1" + ": " + firstComp);
        TLC tlcFirstComp = new TLC();
        timer.reset();
        tlcFirstComp.modelCheckOnlyGoodStates(firstComp, cfg); // TODO there's really no reason to distinguish between the 2 methods
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "State space gen: " + timer.timeElapsed() + "ms");
        Utils.assertNotNull(tlcFirstComp.getLTSBuilder(), "Error generating state space for the first component!");

        // turn the first component into a safety property (interface requirement)
        timer.reset();
        LTS<Integer, String> ltsProp = tlcFirstComp.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "LTS gen: " + timer.timeElapsed() + "ms");
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "# unique states: " + (ltsProp.size() - 1) + " states");
        int totalSumOfStatesChecked = ltsProp.size() - 1;
        int largestProductOfStatesChecked = ltsProp.size() - 1;
        //System.out.println();
        //FSPWriter.INSTANCE.write(System.out, ltsProp);
        //System.out.println();

        // minimize the LTS
        timer.reset();
        ltsProp = AutomataLibUtils.minimizeLTS(ltsProp);
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "minimization: " + timer.timeElapsed() + "ms");
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "# unique states post-minimization: " + (ltsProp.size() - 1) + " states");

        // initialize the alphabet
        AlphabetMembershipTester alphabetTester = new AlphabetMembershipTester(tlcFirstComp.actionsInSpec(), ltsProp);

        if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
            final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
            printMsg = Utils.addPrint(printMsg, ("k: " + 0));
            printMsg = Utils.addPrint(printMsg, ("Total # states checked: " + totalNumStatesChecked));
            printMsg = Utils.addPrint(printMsg, ("Property satisfied!"));
            result.setIfWinner(printMsg, ltsProp);
            return;
        }

        if (SafetyUtils.INSTANCE.hasErrInitState(ltsProp)) {
            final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
            printMsg = Utils.addPrint(printMsg, ("k: " + 0));
            printMsg = Utils.addPrint(printMsg, "Total # states checked: " + totalNumStatesChecked);
            printMsg = Utils.addPrint(printMsg, "Property may be violated.");
            //FSPWriter.INSTANCE.write(System.out, ltsProp);
            result.setIfWinner(printMsg, ltsProp);
            return;
        }
        // at this point, ltsProp represents the interface requirement for the 1st component.
        // therefore, there is no need to look at the 1st component in the following loop.

        for (int i = 1; i < components.size(); ++i) {
            final int compNum = i + 1;
            final String comp = components.get(i);
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "Component " + compNum + ": " + comp);

            TLC tlcComp = new TLC();
            timer.reset();
            tlcComp.modelCheck(comp, noInvsCfg, alphabetTester);
            Utils.addPrintVerbose(printMsg, verbose, "State space gen: " + timer.timeElapsed() + "ms");
            Utils.assertNotNull(tlcComp.getLTSBuilder(), "Error generating state space for component " + compNum + "!");

            // turn the next component into an LTS (user of the interface provided by ltsProp)
            timer.reset();
            LTS<Integer, String> ltsComp = tlcComp.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState();
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "LTS gen: " + timer.timeElapsed() + "ms");
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "# unique states: " + (ltsComp.size() - 1) + " states");
            totalSumOfStatesChecked += ltsComp.size() - 1;
            //System.out.println();
            //FSPWriter.INSTANCE.write(System.out, ltsComp);
            //System.out.println();

            // minimize the LTS for the component
            timer.reset();
            ltsComp = AutomataLibUtils.minimizeLTS(ltsComp);
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "minimization: " + timer.timeElapsed() + "ms");
            printMsg = Utils.addPrintVerbose(printMsg, verbose, "# unique states post-minimization: " + (ltsComp.size() - 1) + " states");
            largestProductOfStatesChecked = Math.max(largestProductOfStatesChecked, ltsProp.size() - 1);

            // remove any actions that are now internal to ltsProp
            // TODO this technically is an abstraction method because later components may have the action
            //Set<String> ltsPropAlphabet = new HashSet<>(ltsProp.getInputAlphabet());
            //ltsPropAlphabet.removeAll(ltsComp.getInputAlphabet());
            //ltsProp = HideUtils.INSTANCE.hideManually(ltsProp, ltsPropAlphabet);

            // create new safety property (interface requirement for all components seen so far)
            timer.reset();
            ltsProp = ParallelComposition.INSTANCE.parallel(ltsComp, ltsProp);
            Utils.printVerbose(verbose, "New property gen (|| composition): " + timer.timeElapsed() + "ms");

            // collect the alphabet
            alphabetTester.update(tlcComp.actionsInSpec(), ltsProp);

            // if the new safety property is TRUE or FALSE then model checking is done
            if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
                final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
                printMsg = Utils.addPrint(printMsg, "");
                printMsg = Utils.addPrint(printMsg, "k: " + i);
                printMsg = Utils.addPrint(printMsg, "Total # states checked: " + totalNumStatesChecked);
                printMsg = Utils.addPrint(printMsg, "Property satisfied!");
                result.setIfWinner(printMsg, ltsProp);
                return;
            }
            if (SafetyUtils.INSTANCE.hasErrInitState(ltsProp)) {
                final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
                Utils.printVerbose(verbose, "");
                printMsg = Utils.addPrint(printMsg, "k: " + i);
                printMsg = Utils.addPrint(printMsg, "Total # states checked: " + totalNumStatesChecked);
                printMsg = Utils.addPrint(printMsg, "Property may be violated.");
                //FSPWriter.INSTANCE.write(System.out, ltsProp);
                result.setIfWinner(printMsg, ltsProp);
                return;
            }
        }

        final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
        printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
        printMsg = Utils.addPrint(printMsg, "k: " + (components.size() - 1));
        printMsg = Utils.addPrint(printMsg, "Total # states checked: " + totalNumStatesChecked);
        printMsg = Utils.addPrint(printMsg, "Property may be violated.");

        // Successful run
        result.setIfWinner(printMsg, ltsProp);


        // encode the sequence of actions that leads to an error in a new TLA+ file	// encode the sequence of actions that leads to an error in a new TLA+ file
        // TODO write error trace for early termination
        writeErrorTraceFile(tla, cfg, result.getLTS());

    }

    // Creates a List of strategies (implementation of different strategies to be completed)
    public static List<RVStrategy> createStrategies(String tla, String cfg, String recompType, String recompFile, boolean verbose, RVResult result) throws InterruptedException {
        List<RVStrategy> strategies = new ArrayList<>();
        if ("PARALLEL".equalsIgnoreCase(recompType)) {
            System.out.println("parallel flag");
            // only adding identity strategy.
            strategies.add(new RVStrategy(tla, cfg, recompType, recompFile, verbose, result));
        } else {
            System.out.println("single threaded");
            RVStrategy sampleStrategy = new RVStrategy(tla, cfg, recompType, recompFile, verbose, result);
            strategies.add(sampleStrategy);
        }
        return strategies;
    }

}
