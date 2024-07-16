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

import static recomp.RVStrategy.createStrategies;

public class RecompVerify {

	public static void runRecompVerify(final String tla, final String cfg, final String recompStrategy, final String recompFile, boolean verbose) {
		// write a config without any invariants / properties
		final String noInvsCfg = "no_invs.cfg";
		Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");

		// Create strategies
        List<RVStrategy> strategies = null;
        try {
            strategies = createStrategies(tla, cfg, recompStrategy, recompFile, verbose);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
		// If strategies is not null create the strategies
        if (strategies != null) {
			for (RVStrategy strategy : strategies) {
				strategy.run();
			}
		}

		// not unix convention, but we use this to signal to the wrapper script that	// not unix convention, but we use this to signal to the wrapper script that
		System.exit(99);
	}

	static void writeErrorTraceFile(final String tla, final String cfg, final LTS<Integer, String> ltsProp) {
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
