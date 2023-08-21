package tlc2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import cmu.isr.assumption.SubsetConstructionGenerator;
import cmu.isr.tolerance.utils.LtsUtils;
import cmu.isr.ts.DetLTS;
import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.ltsa.LTSACall;
import cmu.isr.ts.lts.ltsa.StringLTSInput;
import cmu.isr.ts.lts.ltsa.StringLTSOutput;
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
import net.automatalib.words.impl.Alphabets;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ExtKripke;
import tlc2.tool.impl.FastTool;

public class Composition {
	
	public static LTS<Integer, String> minimizeLTS(LTS<Integer, String> orig) {
    	MinimizationResult<Integer, Property<String, Void>> minResult = Minimizer.minimize( orig.transitionGraphView(orig.getInputAlphabet()) );
    	
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(orig.getInputAlphabet())).create();
    	
    	Map<Integer, Integer> blockToNFAState = new HashMap<>();
    	for (Block<Integer, Property<String, Void>> block : minResult.getBlocks()) {
    		//final Integer origState = minResult.getRepresentative(block);
    		//final boolean isInitState = orig.getInitialStates().contains(origState);
    		//final boolean isAccepting = orig.isAccepting(origState);
    		final boolean isInitState = MinimizationResult.getStatesInBlock(block)
    				.stream()
    				.anyMatch(s -> orig.getInitialStates().contains(s));
    		final boolean isAccepting = MinimizationResult.getStatesInBlock(block)
    				.stream()
    				.allMatch(s -> orig.isAccepting(s));
    		final int nfaState = isInitState ? compactNFA.addInitialState(isAccepting) : compactNFA.addState(isAccepting);
    		//Utils.assertTrue(nfaState == block.getId(), "Mismatch between block ID and compactNFA ID");
    		blockToNFAState.put(block.getId(), nfaState);
    	}
    	
    	for (Block<Integer, Property<String, Void>> srcBlock : minResult.getBlocks()) {
    		final Integer srcNFAState = blockToNFAState.get(srcBlock.getId());
    		//final Integer srcNFAState = srcBlock.getId();
    		final Integer srcOrig = minResult.getRepresentative(srcBlock);
    		for (final String act : orig.getInputAlphabet()) {
    			for (final Integer succOrig : orig.getSuccessors(srcOrig, act)) {
    				final Block<Integer, Property<String, Void>> succBlock = minResult.getBlockForState(succOrig);
    	    		final Integer succNFAState = blockToNFAState.get(succBlock.getId());
    	    		//final Integer succNFAState = succBlock.getId();
    	    		compactNFA.addTransition(srcNFAState, act, succNFAState);
    			}
    		}
    	}
    	
    	return new CompactLTS<>(compactNFA);
	}
    
    public static void decompVerify(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	PerfTimer timer = new PerfTimer();
    	SymbolTable.init();
    	
    	// temporary hack
    	final String noInvsCfg = "no_invs.cfg";
    	Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");
    	
    	final List<String> components = decompAll(tla, cfg);
    	Utils.assertTrue(components.size() > 0, "Decomposition returned no components");
    	System.out.println("# components: " + components.size());
    	
    	final String propComponent = components.get(0);
    	TLC tlcProp = new TLC();
    	timer.reset();
    	tlcProp.modelCheckOnlyGoodStates(propComponent, cfg);
    	System.out.println("prop runTLC: " + timer.timeElapsed());
    	Utils.assertNotNull(tlcProp.getKripke(), "Error generating property / WA for first component");
    	final ExtKripke propKS = tlcProp.getKripke();
    	System.out.println("KS size: " + propKS.size());
    	int totalNumStatesChecked = propKS.size();
    	timer.reset();
    	//DetLTS<Integer, String> ltsProp = propKS.toWeakestAssumptionDFA();
    	LTS<Integer, String> ltsProp = propKS.toWeakestAssumptionDFA();
    	System.out.println("prop WA gen: " + timer.timeElapsed());
    	
    	timer.reset();
    	ltsProp = minimizeLTS(ltsProp);
    	System.out.println("minimize ltsProp: " + timer.timeElapsed());
    	System.out.println("KS size after min: " + ltsProp.size());
    	
    	/*
    	if (ltsProp.propertyIsTrue()) {
			System.out.println("# states checked: " + totalNumStatesChecked);
			System.out.println("WA is true.");
    		System.out.println("Property satisfied!");
    		return;
		}
		else if (ltsProp.propertyIsFalse()) {
			System.out.println("# states checked: " + totalNumStatesChecked);
			System.out.println("WA is false.");
			System.out.println("Property may be violated.");
    		//FSPWriter.INSTANCE.write(System.out, ltsProp);
			return;
		}*/
    	if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
			System.out.println("# states checked: " + totalNumStatesChecked);
			System.out.println("WA is true.");
    		System.out.println("Property satisfied!");
    		return;
    	}
    	// TODO the property will be false if there's a bad initial state
    	
    	// at this point, ltsProp /is/ the WA of the 1st component. therefore, there
    	// is no need to look at the 1st component in the following loop.
    	
    	for (int i = 1; i < components.size(); ++i) {
    		final int iter = i + 1;
    		final String comp = components.get(i);
    		System.out.println();
    		System.out.println("iter " + iter + ": " + comp);
    		
    		TLC tlcComp = new TLC();
    		timer.reset();
        	tlcComp.modelCheck(comp, noInvsCfg);
        	System.out.println("runTLC: " + timer.timeElapsed());
        	Utils.assertNotNull(tlcComp.getKripke(), "Error running TLC on a component");
        	System.out.println("KS size: " + tlcComp.getKripke().size());
        	totalNumStatesChecked += tlcComp.getKripke().size();
        	timer.reset();
        	LTS<Integer, String> ltsComp = tlcComp.getKripke().toNFA();
    		System.out.println("converting KS to NFA: " + timer.timeElapsed());
    		
        	timer.reset();
        	ltsComp = minimizeLTS(ltsComp);
        	System.out.println("minimize ltsComp: " + timer.timeElapsed());
        	System.out.println("KS size after min: " + ltsComp.size());
    		
    		// middle iterations
    		if (i+1 < components.size()) {
        		timer.reset();
        		SubsetConstructionGenerator<String> waGen = new SubsetConstructionGenerator<>(ltsComp, ltsProp);
        		ltsProp = waGen.generate(true);
        		System.out.println("WA gen: " + timer.timeElapsed());
        		
        		// TODO should we be minimizing ltsProp here now too?
        		/*
        		timer.reset();
            	ltsProp = minimizeLTS(ltsProp);
            	System.out.println("minimize ltsProp: " + timer.timeElapsed());
            	System.out.println("KS size after min: " + ltsProp.size());*/
        		
        		/*
        		if (ltsProp.propertyIsTrue()) {
        			System.out.println("# states checked: " + totalNumStatesChecked);
        			System.out.println("WA is true.");
            		System.out.println("Property satisfied!");
            		return;
        		}
        		else if (ltsProp.propertyIsFalse()) {
        			System.out.println("# states checked: " + totalNumStatesChecked);
        			System.out.println("WA is false.");
        			System.out.println("Property may be violated.");
            		//FSPWriter.INSTANCE.write(System.out, ltsProp);
        			return;
        		}*/
            	if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
        			System.out.println("# states checked: " + totalNumStatesChecked);
        			System.out.println("WA is true.");
            		System.out.println("Property satisfied!");
            		return;
            	}
            	// TODO the property will be false if there's a bad initial state
    		}
			// for the final iteration, we use model checking since it's faster than
	    	// generating the WA
    		else {
        		timer.reset();
    			//if (LtsUtils.INSTANCE.satisfiesNoCopy(ltsComp, ltsProp)) {
        		if (SafetyUtils.INSTANCE.satisfiesNotProp(ltsComp, ltsProp)) {
            		System.out.println("Final MC: " + timer.timeElapsed());
        			System.out.println("# states checked: " + totalNumStatesChecked);
            		System.out.println("Property satisfied!");
            		return;
    			}
        		System.out.println("Final MC: " + timer.timeElapsed());
    		}
    	}
		System.out.println("# states checked: " + totalNumStatesChecked);
		System.out.println("Property may be violated.");
    }
    
    public static void decompVerifyUniform(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	PerfTimer timer = new PerfTimer();
    	SymbolTable.init();
    	
    	// temporary hack
    	final String noInvsCfg = "no_invs.cfg";
    	Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");

    	final List<String> components = decompAll(tla, cfg);
    	Utils.assertTrue(components.size() > 0, "Decomposition returned no components");
    	System.out.println("# components: " + components.size());
    	
    	final String propComponent = components.get(0);
    	TLC tlcProp = new TLC();
    	timer.reset();
    	tlcProp.modelCheck(propComponent, cfg);
    	System.out.println("prop runTLC: " + timer.timeElapsed());
    	Utils.assertNotNull(tlcProp.getKripke(), "Error generating property / WA for first component");
    	final ExtKripke propKS = tlcProp.getKripke();
    	timer.reset();
    	DetLTS<Integer, String> ltsProp = propKS.toWeakestAssumptionNoSinkDFA();
    	System.out.println("prop WA gen: " + timer.timeElapsed());
    	
    	if (ltsProp.propertyIsTrue()) {
    		System.out.println("Property satisfied!");
    		return;
		}
		else if (ltsProp.propertyIsFalse()) {
			System.out.println("Property may be violated.");
    		//FSPWriter.INSTANCE.write(System.out, ltsProp);
			return;
		}
    	
    	for (int i = 0; i < components.size(); ++i) {
    		final int iter = i + 1;
    		final String comp = components.get(i);
    		System.out.println();
    		System.out.println("iter " + iter + ": " + comp);
    		
    		TLC tlcComp = new TLC();
    		timer.reset();
    		tlcComp.modelCheck(comp, noInvsCfg);
        	System.out.println("runTLC: " + timer.timeElapsed());
        	Utils.assertNotNull(tlcComp.getKripke(), "Error running TLC on a component");
        	timer.reset();
        	LTS<Integer, String> ltsComp = tlcComp.getKripke().toNFA();
    		System.out.println("converting KS to NFA: " + timer.timeElapsed());
    		
    		// middle iterations
    		if (i+1 < components.size()) {
        		timer.reset();
        		SubsetConstructionGenerator<String> waGen = new SubsetConstructionGenerator<>(ltsComp, ltsProp);
        		//ltsProp = waGen.generate(true);
        		System.out.println("WA gen: " + timer.timeElapsed());
            		
        		if (ltsProp.propertyIsTrue()) {
        			System.out.println("WA is true.");
            		System.out.println("Property satisfied!");
            		return;
        		}
        		else if (ltsProp.propertyIsFalse()) {
        			System.out.println("WA is false.");
        			System.out.println("Property may be violated.");
            		//FSPWriter.INSTANCE.write(System.out, ltsProp);
        			return;
        		}
    		}
			// for the final iteration, we use model checking since it's faster than
	    	// generating the WA
    		else {
        		timer.reset();
    			if (LtsUtils.INSTANCE.satisfiesNoCopy(ltsComp, ltsProp)) {
            		System.out.println("Final MC: " + timer.timeElapsed());
            		System.out.println("Property satisfied!");
            		return;
    			}
        		System.out.println("Final MC: " + timer.timeElapsed());
    		}
    	}
		System.out.println("Property may be violated.");
    }
    
    public static void toFSP(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	//final long calcStart = System.currentTimeMillis();
    	
    	// initialize and run TLC
    	TLC tlc = new TLC("tlc");
    	tlc.modelCheck(tla, cfg);
    	
    	// error checking
    	if (tlc.getKripke() == null) {
    		System.err.println("The spec is malformed, or the file does not exist.");
    		return;
    	}
    	//final long calcEnd = System.currentTimeMillis();
    	//final long writeStart = System.currentTimeMillis();
    	System.out.println(tlc.getKripke().toFSP());
    	//final long writeEnd = System.currentTimeMillis();
    	//System.err.println("to-fsp # states: " + tlc.getKripke().reach().size());
    	//System.err.println("to-fsp calc time: " + (calcEnd - calcStart));
    	//System.err.println("to-fsp write time: " + (writeEnd - writeStart));
    }
    
    public static void weakestAssumptionNoSink(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC("tlc");
    	tlc.modelCheck(tla, cfg);
    	
    	// error checking
    	if (tlc.getKripke() == null) {
    		System.err.println("The spec is malformed, or the file does not exist.");
    		return;
    	}
    	System.out.println(tlc.getKripke().weakestAssumptionNoSink());
    }
    
    public static String composeSpecs(String[] args) {
		final String tla1 = args[1];
		final String cfg1 = args[2];
		final String tla2 = args[3];
		final String cfg2 = args[4];
		return ExtKripke.composeSpecs(tla1, cfg1, tla2, cfg2);
    }


    public static void decompose(String[] args) {
    	String tla = args[1];
    	String cfg = args[2];
    	decompAll(tla, cfg);
    }
    
    private static Set<String> stateVarsInSpec(final String tla, final String cfg) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("sv_" + tla);
    	tlc.initialize(tla, cfg);
    	return tlc.stateVarsInSpec();
    }
    
    private static Set<String> actionsInSpec(final String tla, final String cfg) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("act_" + tla);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	return Utils.toArrayList(ft.getActions())
        		.stream()
        		.map(a -> a.getName().toString())
        		.collect(Collectors.toSet());
    }
    
    
    /* Decomp helpers */
    
    private static List<String> decompAll(String tla, String cfg) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	
    	// get state vars to decompose with
    	Set<String> invariantVars = tlc.stateVariablesUsedInInvariants();
    	Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(invariantVars);
    	Set<String> allVars = stateVarsInSpec(tla, cfg);
    	Set<String> nonPropertyVars = Utils.setMinus(allVars, propertyVars);
    	
    	List<String> components = new ArrayList<>();
    	int iter = 1;
    	while (propertyVars.size() > 0 && nonPropertyVars.size() > 0) {
    		final String aSpec = "A" + iter;
    		final String bSpec = "B" + iter;
    		decompose(aSpec, propertyVars, tla, cfg, true);
        	decompose(bSpec, nonPropertyVars, tla, cfg, false);
        	components.add(aSpec);
        	
        	allVars = stateVarsInSpec(bSpec, "no_invs.cfg");
        	propertyVars = calcPropertyVars(aSpec, "no_invs.cfg", bSpec, "no_invs.cfg");
        	nonPropertyVars = Utils.setMinus(allVars, propertyVars);
        	tla = bSpec;
        	cfg = "no_invs.cfg";
        	++iter;
    	}
    	
    	components.add("B" + (iter-1));
    	return components;
    }
    
    /**
     * Calculates the vars from bSpec that /may/ be needed to uphold the guarantees of the interface
     * provided in aSpec. We perform this calculation by consider all variables in bSpec that are not
     * exclusively in UNCHANGED blocks in the mutual actions of aSpec and bSpec.
     * @param aSpec
     * @param bSpec
     * @return
     */
    private static Set<String> calcPropertyVars(final String aSpec, final String aCfg, final String bSpec, final String bCfg) {
    	final Set<String> aActions = actionsInSpec(aSpec, aCfg);
    	final Set<String> bActions = actionsInSpec(bSpec, bCfg);
    	final Set<String> ifaceActions = Utils.intersection(aActions, bActions);
    	
    	TLC tlc = new TLC("b_" + bSpec);
    	tlc.initialize(bSpec, bCfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// get the top level module and all op def nodes
    	final String moduleName = tlc.getModelName();
    	final ModuleNode mn = ft.getModule(moduleName);
    	List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
    			.stream()
    			.filter(d -> !d.isStandardModule())
    			.collect(Collectors.toList());
    	
    	// find vars that are always unchanged in ifaceActions in bSpec
    	final Set<String> bVars = stateVarsInSpec(bSpec, bCfg);
    	final Set<String> unchangedBVars = bVars
    			.stream()
    			.filter(v -> {
    				return moduleNodes
    						.stream()
    						.filter(n -> ifaceActions.contains(n.getName().toString())) // only consider actions in the iface
    						.allMatch(n -> n.varIsUnchanged(v));
    			})
    			.collect(Collectors.toSet());
    	
    	// find the vars that may be changed in ifaceActions in bSpec
    	final Set<String> varsThatMayChange = Utils.setMinus(bVars, unchangedBVars);
    	
    	// also compute all vars that occur in the same expressions as varsThatMayChange
    	final Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(varsThatMayChange);
    	return propertyVars;
    }
    
    private static void decompose(final String specName, final Set<String> keepVars, final String tla, final String cfg, boolean includeInvs) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC(specName);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// TODO we could definitely mine this from the spec
    	final String nextName = "Next";
    	
    	// calculate variables to remove from the spec
    	final Set<String> allVars = Utils.toArrayList(ft.getVarNames())
        		.stream()
        		.collect(Collectors.toSet());
    	final Set<String> removeVars = Utils.setMinus(allVars, keepVars);
    	
    	// get the actions and invariants in the spec
		final Set<String> actionNames = Utils.toArrayList(ft.getActions())
				.stream()
				.map(a -> a.getName().toString())
				.filter(a -> !a.equals(nextName)) // the "Next" transition relation should not be filtered out
				.collect(Collectors.toSet());
		final Set<String> invariants = Utils.toArrayList(ft.getInvNames())
				.stream()
				.collect(Collectors.toSet());
    	
    	// get the top level module and all op def nodes
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				.filter(d -> !d.isStandardModule())
				.filter(d -> includeInvs ? true : !invariants.contains(d.getName().toString()))
				.collect(Collectors.toList());
		
		// remove all vars in the module from removeVars
		for (OpDefNode n : moduleNodes) {
			n.removeStateVarsFromUnchangedTuples(removeVars);
			n.removeConjunctsWithEmptyUnchangedOp();
			n.removeConjunctsWithStateVars(removeVars);
			n.removeChildrenWithName(removeVars);
			n.removeUnusedLetDefs();
		}
		
		// .filter(d -> !d.emptyNode())
		
		// remove any actions that become empty from removing the vars in removeVars
		final Set<OpDefNode> actionNodesToRemove = moduleNodes
				.stream()
				.filter(n -> actionNames.contains(n.getName().toString()))
				.filter(n -> n.hasOnlyUnchangedConjuncts())
				.collect(Collectors.toSet());
		final Set<String> actionNodeNamesToRemove = actionNodesToRemove
				.stream()
				.map(n -> n.getName().toString())
				.collect(Collectors.toSet());
		for (OpDefNode n : moduleNodes) {
			n.removeChildrenWithName(actionNodeNamesToRemove);
		}
		
		// create TLA+ from the node defs
		final String specBody = moduleNodes
				.stream()
				.filter(d -> !actionNodesToRemove.contains(d))
				.map(d -> d.toTLA())
				.collect(Collectors.joining("\n\n"));
		
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());

        final String moduleList = String.join(", ", moduleNameList);
        final String varList = String.join(", ", keepVars);
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(endModule).append("\n");

        final String fileName = specName + ".tla";
        final String file = fileName;
        //final String file = outputLoc + fileName;
        Utils.writeFile(file, builder.toString());
    }
    
    private static DetLTS<Integer, String> fspToDFA(final String fsp) {
    	StringLTSOutput ltsOutput = new StringLTSOutput();
    	LTSCompiler ltsCompiler = new LTSCompiler(new StringLTSInput(fsp), ltsOutput, System.getProperty("user.dir"));
    	CompositeState lts = ltsCompiler.compile("DEFAULT");
    	lts.compose(ltsOutput);
    	return LTSACall.INSTANCE.toDetLTS(lts, false);
    }
    
    private static LTS<Integer, String> fspToNFA(final String fsp) {
    	StringLTSOutput ltsOutput = new StringLTSOutput();
    	LTSCompiler ltsCompiler = new LTSCompiler(new StringLTSInput(fsp), ltsOutput, System.getProperty("user.dir"));
    	CompositeState lts = ltsCompiler.compile("DEFAULT");
    	lts.compose(ltsOutput);
    	return LTSACall.INSTANCE.toLTS(lts, false);
    }

    // code for accessing the init state!
	// decompose init state based on state vars in propertyVars
	//Utils.assertTrue(ft.getInitStateSpec().size() == 1, "There should be exactly one init state predicate!");
	//final Action initAct = ft.getInitStateSpec().elementAt(0);
	//initAct.getOpDef().removeConjunctsWithoutStateVars(propertyVars);
}
