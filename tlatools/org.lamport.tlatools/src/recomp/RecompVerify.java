package recomp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import cmu.isr.assumption.SubsetConstructionGenerator;
import cmu.isr.tolerance.utils.LtsUtils;
import cmu.isr.ts.DetLTS;
import cmu.isr.ts.LTS;
import cmu.isr.ts.ParallelComposition;
import cmu.isr.ts.lts.ltsa.LTSACall;
import cmu.isr.ts.lts.ltsa.StringLTSInput;
import cmu.isr.ts.lts.ltsa.StringLTSOutput;
import cmu.isr.ts.nfa.HideUtils;
import cmu.isr.ts.lts.CompactLTS;
import cmu.isr.ts.lts.SafetyUtils;
import cmu.isr.ts.lts.ltsa.FSPWriter;
import lts.CompositeState;
import lts.LTSCompiler;
import lts.LTSInputString;
import lts.SymbolTable;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.automata.graphs.TransitionEdge.Property;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.util.minimizer.Block;
import net.automatalib.util.minimizer.MinimizationResult;
import net.automatalib.util.minimizer.Minimizer;
import net.automatalib.words.Word;
import net.automatalib.words.impl.Alphabets;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.AlphabetMembershipTester;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.Utils.Pair;
import tlc2.tool.ExtKripke;
import tlc2.tool.impl.FastTool;

public class RecompVerify implements Runnable {

	public static boolean globalIsDone = false;

	@ Override
	public void run() {
		try {
			Thread.sleep(100);
		}
		catch (InterruptedException e) {
			System.out.println("Thread interrupted");
		}
		if (isThreadDone()){
			System.out.println("Program executed within: " + "{Some time}" + " ms.");
		}
		return ;
	}

	synchronized public boolean isThreadDone() {
		boolean isDone = globalIsDone;
		globalIsDone = true;
		return isDone;
	}

	public static void recompVerify(final String tla, final String cfg, final String recompType, final String recompFile, boolean verbose) {
    	PerfTimer timer = new PerfTimer();
    	SymbolTable.init();

    	// write a config without any invariants / properties
    	final String noInvsCfg = "no_invs.cfg";
    	Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");


    	// decompose the spec into as many components as possible
		final List<String> rawComponents = Decomposition.decompAll(tla, cfg);
		runRecompMap(tla, cfg, recompType,  recompFile, verbose, rawComponents);
    }


	private static void runRecompMap(final String tla, final String cfg, final String recompType, final String recompFile, boolean verbose, final List<String> rawComponents) {
		String printMsg =  "";

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
		printMsg = Utils.addPrintVerbose(printMsg, verbose, "# unique states: " + (ltsProp.size()-1) + " states");
		int totalSumOfStatesChecked = ltsProp.size() - 1;
		int largestProductOfStatesChecked = ltsProp.size() - 1;
		//System.out.println();
		//FSPWriter.INSTANCE.write(System.out, ltsProp);
		//System.out.println();

		// minimize the LTS
		timer.reset();
		ltsProp = AutomataLibUtils.minimizeLTS(ltsProp);
		printMsg = Utils.addPrintVerbose(printMsg, verbose, "minimization: " + timer.timeElapsed() + "ms");
		printMsg = Utils.addPrintVerbose(printMsg, verbose, "# unique states post-minimization: " + (ltsProp.size()-1) + " states");

		// initialize the alphabet
		AlphabetMembershipTester alphabetTester = new AlphabetMembershipTester(tlcFirstComp.actionsInSpec(), ltsProp);
		
		if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
			final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
			printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
			printMsg = Utils.addPrint(printMsg, ("k: " + 0));
			printMsg = Utils.addPrint(printMsg, ("Total # states checked: " + totalNumStatesChecked));
			printMsg = Utils.addPrint(printMsg, ("Property satisfied!"));
			return;
		}

		if (SafetyUtils.INSTANCE.hasErrInitState(ltsProp)) {
			final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
			printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
			printMsg = Utils.addPrint(printMsg, ("k: " + 0));
			printMsg = Utils.addPrint(printMsg, "Total # states checked: " + totalNumStatesChecked);
			printMsg = Utils.addPrint(printMsg, "Property may be violated.");
			//FSPWriter.INSTANCE.write(System.out, ltsProp);
			System.out.print(printMsg);
			return;
		}

		// at this point, ltsProp represents the interface requirement for the 1st component.
		// therefore, there is no need to look at the 1st component in the following loop.

		for (int i = 1; i < components.size(); ++i) {
			final int compNum = i + 1;
			final String comp = components.get(i);
			printMsg = Utils.addPrintVerbose(printMsg, verbose, "");
			printMsg = Utils.addPrintVerbose(printMsg,verbose, "Component " + compNum + ": " + comp);

			TLC tlcComp = new TLC();
			timer.reset();
			tlcComp.modelCheck(comp, noInvsCfg, alphabetTester);
			Utils.addPrintVerbose(printMsg,verbose, "State space gen: " + timer.timeElapsed() + "ms");
			Utils.assertNotNull(tlcComp.getLTSBuilder(), "Error generating state space for component " + compNum + "!");

			// turn the next component into an LTS (user of the interface provided by ltsProp)
			timer.reset();
			LTS<Integer, String> ltsComp = tlcComp.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState();
			printMsg = Utils.addPrintVerbose(printMsg,verbose, "LTS gen: " + timer.timeElapsed() + "ms");
			printMsg = Utils.addPrintVerbose(printMsg,verbose, "# unique states: " + (ltsComp.size()-1) + " states");
			totalSumOfStatesChecked =ltsComp.size() - 1;
			//System.out.println();
			//FSPWriter.INSTANCE.write(System.out, ltsComp);
			//System.out.println();

			// minimize the LTS for the component
			timer.reset();
			ltsComp = AutomataLibUtils.minimizeLTS(ltsComp);
			printMsg = Utils.addPrintVerbose(printMsg, verbose,"minimization: " + timer.timeElapsed() + "ms");
			printMsg = Utils.addPrintVerbose(printMsg, verbose,"# unique states post-minimization: " + (ltsComp.size()-1) + " states");
			largestProductOfStatesChecked = Math.max(largestProductOfStatesChecked, ltsProp.size()-1);

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
				printMsg = Utils.addPrint(printMsg,  "");
				printMsg = Utils.addPrint(printMsg, "k: " + i);
				printMsg = Utils.addPrint(printMsg,"Total # states checked: " + totalNumStatesChecked);
				printMsg = Utils.addPrint(printMsg,"Property satisfied!");
				System.out.print(printMsg);
				return;
			}
			if (SafetyUtils.INSTANCE.hasErrInitState(ltsProp)) {
				final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
				Utils.printVerbose(verbose, "");
				printMsg = Utils.addPrint(printMsg,"k: " + i);
				printMsg = Utils.addPrint(printMsg,"Total # states checked: " + totalNumStatesChecked);
				printMsg = Utils.addPrint(printMsg,"Property may be violated.");
				//FSPWriter.INSTANCE.write(System.out, ltsProp);
				System.out.print(printMsg);
				return;
			}
		}
		final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
		Utils.printVerbose(verbose, "");
		printMsg = Utils.addPrint(printMsg,"k: " + (components.size() - 1));
		printMsg = Utils.addPrint(printMsg,"Total # states checked: " + totalNumStatesChecked);
		printMsg = Utils.addPrint(printMsg,"Property may be violated.");


		//Output everything
		System.out.print(printMsg);
		
		// encode the sequence of actions that leads to an error in a new TLA+ file	// encode the sequence of actions that leads to an error in a new TLA+ file
		// TODO write error trace for early termination	// TODO write error trace for early termination
		writeErrorTraceFile(tla, cfg, ltsProp);	writeErrorTraceFile(tla, cfg, ltsProp);

		// not unix convention, but we use this to signal to the wrapper script that	// not unix convention, but we use this to signal to the wrapper script that
		// it should produce an error trace	// it should produce an error trace
		System.exit(99);	System.exit(99);
	}


	private static void writeErrorTraceFile(final String tla, final String cfg, final LTS<Integer, String> ltsProp) {
		final Word<String> trace = SafetyUtils.INSTANCE.findErrorTrace(ltsProp);
		/*System.out.println("Error trace:");
		for (final String act : trace) {
			System.out.println("  " + act);
		}*/
		ArrayList<String> errFile = Utils.fileContents(tla);
		int moduleIdx = -1;
		for (int i = 0; i < errFile.size(); ++i) {
			final String line = errFile.get(i);
			//if (line.trim().matches("\\Q----\\E")) {
			if (line.trim().substring(0, 4).equals("----")) {
				moduleIdx = i;
				errFile.set(i, "---- MODULE ErrTrace ----");
				break;
			}
		}

		int extendsIdx = -1;
		for (int i = 0; i < errFile.size(); ++i) {
			final String line = errFile.get(i);
			//if (line.trim().matches("\\Q----\\E")) {
			if (line.contains("EXTENDS")) {
				extendsIdx = i;
				break;
			}
		}
		if (extendsIdx >= 0) {
			final String extLine = errFile.get(extendsIdx);
			if (!extLine.contains("Naturals")) {
				final String extWithNaturals = extLine + ", Naturals";
				errFile.set(extendsIdx, extWithNaturals);
			}
		}
		else {
			errFile.add(moduleIdx+1, "EXTENDS Naturals");
		}

		int eofIdx = errFile.size() - 1;
		for ( ; eofIdx >= 0; --eofIdx) {
			final String line = errFile.get(eofIdx);
			// at least four consecutive ='s for the EOF
			//if (line.trim().matches("\\Q====\\E")) {
			if (line.trim().substring(0, 4).equals("====")) {
				break;
			}
		}
		Utils.assertTrue(eofIdx > 0, "Unable to find the EOF in the TLA+ file!");

		errFile.add(eofIdx++, "VARIABLE errCounter");
		errFile.add(eofIdx++, "ErrInit ==");
		errFile.add(eofIdx++, "    /\\ Init");
		errFile.add(eofIdx++, "    /\\ errCounter = 0");
		errFile.add(eofIdx++, "ErrNext ==");
		errFile.add(eofIdx++, "    /\\ Next");
		errFile.add(eofIdx++, "    /\\ errCounter' = errCounter + 1");

		int c = 0;
		for (final String act : trace) {
			final ArrayList<String> actParts = Utils.toArrayList(act.split("\\."));
			Utils.assertTrue(actParts.size() > 0, "actParts has size 0!");
			StringBuilder actBuilder = new StringBuilder();
			actBuilder.append(actParts.get(0));
			if (actParts.size() > 1) {
				actParts.remove(0);
				final String params = actParts
					.stream()
					.map(p -> {
						try {
							Integer.parseInt(p);
						} catch (NumberFormatException e) {
							return "\"" + p + "\"";
						}
						return p;
					})
					.collect(Collectors.joining(","));
				actBuilder.append("(");
				actBuilder.append(params);
				actBuilder.append(")");
			}
			errFile.add(eofIdx++, "    /\\ (errCounter = " + c++ + ") => " + actBuilder.toString());
		}

		errFile.add(eofIdx++, "    /\\ (errCounter = " + c + ") => FALSE");
		errFile.add(eofIdx++, "ErrSpec == ErrInit /\\ [][ErrNext]_vars");

		final String errFileContents = String.join("\n", errFile);
		Utils.writeFile("ErrTrace.tla", errFileContents);

		// write the cfg file
		StringBuilder errCfg = new StringBuilder();
		errCfg.append("SPECIFICATION ErrSpec");

    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	FastTool ft = (FastTool) tlc.tool;
    	for (final String inv : ft.getInvNames()) {
    		errCfg.append("\nINVARIANT ").append(inv);
    	}
    	Utils.writeFile("ErrTrace.cfg", errCfg.toString());
	}
}
