package tlc2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
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
import tlc2.tool.ExtKripke;
import tlc2.tool.impl.FastTool;

public class Composition {
	
	private static LTS<Integer, String> minimizeLTS(LTS<Integer, String> orig) {
    	MinimizationResult<Integer, Property<String, Void>> minResult = Minimizer.minimize( orig.transitionGraphView(orig.getInputAlphabet()) );
    	
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(orig.getInputAlphabet())).create();
    	
    	Map<Integer, Integer> blockToNFAState = new HashMap<>();
    	for (Block<Integer, Property<String, Void>> block : minResult.getBlocks()) {
    		final boolean isInitState = MinimizationResult.getStatesInBlock(block)
    				.stream()
    				.anyMatch(s -> orig.getInitialStates().contains(s));
    		final boolean isAccepting = MinimizationResult.getStatesInBlock(block)
    				.stream()
    				.allMatch(s -> orig.isAccepting(s));
    		final int nfaState = isInitState ? compactNFA.addInitialState(isAccepting) : compactNFA.addState(isAccepting);
    		blockToNFAState.put(block.getId(), nfaState);
    	}
    	
    	for (Block<Integer, Property<String, Void>> srcBlock : minResult.getBlocks()) {
    		final Integer srcNFAState = blockToNFAState.get(srcBlock.getId());
    		final Integer srcOrig = minResult.getRepresentative(srcBlock);
    		for (final String act : orig.getInputAlphabet()) {
    			for (final Integer succOrig : orig.getSuccessors(srcOrig, act)) {
    				final Block<Integer, Property<String, Void>> succBlock = minResult.getBlockForState(succOrig);
    	    		final Integer succNFAState = blockToNFAState.get(succBlock.getId());
    	    		compactNFA.addTransition(srcNFAState, act, succNFAState);
    			}
    		}
    	}
    	
    	return new CompactLTS<>(compactNFA);
	}
	
	private static List<String> interfaceOrdering(final List<String> rawComponents) {
		if (rawComponents.isEmpty()) {
			return rawComponents;
		}
		
    	final String noInvsCfg = "no_invs.cfg";
    	final List<Set<String>> alphabets = rawComponents
    			.stream()
    			.map(c -> actionsInSpec(c, noInvsCfg))
    			.collect(Collectors.toList());
    	
    	// gather all components that use the interface of the current component Ci
    	final Set<Integer> allIndices =
    			IntStream
    			.range(0, rawComponents.size())
    		    .boxed()
    		    .collect(Collectors.toSet());
    	Set<String> alphSoFar = new HashSet<>();
    	List<String> components = new ArrayList<>();
    	Set<Integer> indicesInPlace = new HashSet<>();
    	
    	// place the first component at the front
    	components.add(rawComponents.get(0));
    	indicesInPlace.add(0);
		alphSoFar.addAll(alphabets.get(0));
    	
    	// place all components
    	while (!indicesInPlace.containsAll(allIndices)) {
    		// find the components whose alphabet intersects with alphSoFar
    		final Set<Integer> interfaceIndices = Utils.setMinus(allIndices, indicesInPlace)
    				.stream()
    				.filter(i -> !Utils.intersection(alphabets.get(i), alphSoFar).isEmpty())
    				.collect(Collectors.toSet());
    		if (interfaceIndices.isEmpty()) {
    			// if no components intersect with the prior alphabet then it can't affect verification
    			break;
    		}
    		interfaceIndices
					.stream()
					.forEach(i -> {
						components.add(rawComponents.get(i));
						alphSoFar.addAll(alphabets.get(i));
					});
			indicesInPlace.addAll(interfaceIndices);
    	}
    	
    	return components;
	}
	
	private static String makeIntoSpec(final String specName, final String specBody) {
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append("\n");
        builder.append(specBody);
        builder.append("\n");
        builder.append(endModule).append("\n");
        return builder.toString();
    }
    
    private static List<String> decompForSymbolicCompose(String tla, String cfg, final List<List<String>> componentGroupings, boolean allComponents) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	
    	// get state vars to decompose with
    	
    	List<String> components = new ArrayList<>();
    	final int maxIter = allComponents ? componentGroupings.size()-1 : componentGroupings.size();
    	int iter = 0;
    	for (int i = 0; i < maxIter; ++i) {
    		final String aSpec = "D" + iter;
    		final String bSpec = "E" + iter;

        	final Set<String> allVars = stateVarsInSpec(tla, cfg);
        	final Set<String> propertyVars = componentGroupings.get(i)
        			.stream()
        			.map(c -> stateVarsInSpec(c, "no_invs.cfg"))
        			.reduce((Set<String>) new HashSet<String>(),
        					(acc, s) -> Utils.union(acc, s),
        					(s, t) -> Utils.union(s, t));
        	final Set<String> nonPropertyVars = Utils.setMinus(allVars, propertyVars);
    		
    		slice(aSpec, propertyVars, tla, cfg, true);
    		slice(bSpec, nonPropertyVars, tla, cfg, false);
        	components.add(aSpec);
        	
        	final List<String> group = componentGroupings.get(i);
        	final String composedStr = String.join(" || ", group);
			System.err.println(aSpec + " = " + composedStr);
			
        	tla = bSpec;
        	cfg = "no_invs.cfg";
        	++iter;
    	}
    	
    	if (iter > 0) {
    		// we decomposed into at least two components
    		if (allComponents) {
        		final int finalIter = iter - 1;
        		final String name = "E";
            	components.add(name + finalIter);

        		final int finalIdx = iter;
            	final List<String> finalGroup = componentGroupings.get(finalIdx);
            	final String composedStr = String.join(" || ", finalGroup);
    			System.err.println(name + finalIter + " = " + composedStr);
    		}
    	}
    	else {
    		// we were not able to decompose the spec. perform monolithic MCing
    		components.add(tla);
    	}
    	return components;
    }
	
	private static List<String> symbolicComposeByTypeOK(final String tla, final String cfg, final List<String> rawComponents) {
    	final String noInvsCfg = "no_invs.cfg";
    	
		// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC(tla);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
    	
    	// find TypeOK, if it exists
		final List<OpDefNode> typeOkModuleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(m -> m.getName().toString().toLowerCase().equals("typeok"))
				.collect(Collectors.toList());
		
		Utils.assertTrue(typeOkModuleNodes.size() <= 1, "Multiple TypeOK definitions found in the Spec!");
		if (typeOkModuleNodes.isEmpty()) {
			System.err.println("No TypeOK in the Spec, can't apply heuristic 1");
			return rawComponents;
		}
		final OpDefNode typeOkDef = typeOkModuleNodes.get(0);
		
		// group state variables by their type
		final Map<String,String> varTypes = typeOkDef.collectTypesFromTypeOK(); // var -> type
		final Collection<Set<String>> varGroupings = varTypes // set(set(var))
				.entrySet()
				.stream()
				.collect(Collectors.groupingBy(Map.Entry::getValue, Collectors.mapping(Map.Entry::getKey, Collectors.toSet())))
				.values();
		
		// compose components whose variables have the same types
		Map<String, Set<String>> componentStateVars = new HashMap<>();
		for (final String c : rawComponents) {
			componentStateVars.put(c, stateVarsInSpec(c, noInvsCfg));
		}
		
		Set<String> groupedComponents = new HashSet<>();
		final List<List<String>> componentGroupings = varGroupings
				.stream()
				.map(g -> {
					final List<String> componentGroup = rawComponents
							.stream()
							.filter(c -> !groupedComponents.contains(c))
							.filter(c -> !Utils.intersection(componentStateVars.get(c), g).isEmpty())
							.collect(Collectors.toList());
					groupedComponents.addAll(componentGroup);
					return componentGroup;
				})
				.filter(g -> !g.isEmpty())
				.collect(Collectors.toList());
		
		// make sure the c1 component (which contains the property vars) comes first
		final String c1 = rawComponents.get(0);
		for (final List<String> grouping : componentGroupings) {
			final Set<String> groupingSet = grouping.stream().collect(Collectors.toSet());
			if (groupingSet.contains(c1)) {
				componentGroupings.remove(grouping);
				componentGroupings.add(0, grouping);
				break;
			}
		}
		
		return decompForSymbolicCompose(tla, cfg, componentGroupings, true);
		
		/*
		List<String> components = new ArrayList<>();
		final String baseFileName = "D";
		for (int i = 0; i < componentGroupings.size(); ++i) {
			final String groupFileName = baseFileName + i;
			final String tlaGroupFileName = groupFileName + ".tla";
			final List<String> group = componentGroupings.get(i);
			
			String prevComponent = group.get(0);
			for (int j = 1; j < group.size(); ++j) {
				final String nextComponent = group.get(j);
				final String componentFileName = groupFileName + "_" + j;
				final String tlaComponentFileName = componentFileName + ".tla";
				
				final String composedBody = ExtKripke.composeSpecs(prevComponent, noInvsCfg, nextComponent, noInvsCfg);
				final String composed = makeIntoSpec(componentFileName, composedBody);
				
				Utils.writeFile(tlaComponentFileName, composed);
				prevComponent = tlaComponentFileName;
			}
			
			Utils.copyFile(prevComponent, tlaGroupFileName);
			components.add(groupFileName);
			
			final String composedStr = String.join(" || ", group);
			System.err.println(groupFileName + " = " + composedStr);
		}
		
		return components;*/
	}
	
	private static List<String> symbolicCompose(final String tla, final String cfg, boolean customSymComp, final List<String> rawComponents) {
		//return symbolicComposeByTypeOK(tla, cfg, interfaceOrdering(rawComponents));
		//return interfaceOrdering(symbolicComposeByTypeOK(tla, cfg, interfaceOrdering(rawComponents)));
		//return interfaceOrdering(rawComponents);
		//return rawComponents;
		
		// interfaceOrdering() trims unneeded components. Don't use the ordering, but do use it to trim components.
		final Set<String> neededComponents = interfaceOrdering(rawComponents).stream().collect(Collectors.toSet());
		final List<String> trimmedComponents = rawComponents
				.stream()
				.filter(c -> neededComponents.contains(c))
				.collect(Collectors.toList());
		final boolean allCompoments = trimmedComponents.size() == rawComponents.size();
		
		List<List<String>> groupings = new ArrayList<>();

		// consensus_forall
		//customGroupings.add(List.of("C1", "C5", "C3", "C2", "T5"));
		//customGroupings.add(List.of("C4"));
		
		// custom grouping
		if (customSymComp) {
			Utils.fileContents("custom_sym_comp.csv")
				.stream()
				.map(l -> Utils.toArrayList(l.split(",")))
				.map(a -> a.stream().map(c -> c.trim()).collect(Collectors.toList()))
				.forEach(a -> groupings.add(a));
			
			// sanity check
			final Set<String> rawCmptSet = trimmedComponents.stream().collect(Collectors.toSet());
			final Set<String> grCmptSet = groupings
					.stream()
					.reduce((Set<String>) new HashSet<String>(),
							(acc, g) -> Utils.union(acc, g.stream().collect(Collectors.toSet())),
							(s, t) -> Utils.union(s, t));
			if (!grCmptSet.equals(rawCmptSet)) {
				// some extra debugging info for the user
				System.err.println("Components expected:");
				for (String s : rawCmptSet) {
					System.err.println("  " + s);
				}
				System.err.println("Components seen:");
				for (String s : grCmptSet) {
					System.err.println("  " + s);
				}
				Utils.assertTrue(false, "Invalid custom grouping!");
			}
		}
		// default grouping
		else {
			for (final String c : trimmedComponents) {
				groupings.add(List.of(c));
			}
		}
		
		return decompForSymbolicCompose(tla, cfg, groupings, allCompoments);
	}
    
	public static void decompVerify(String[] args, boolean customSymComp) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	PerfTimer timer = new PerfTimer();
    	SymbolTable.init();
    	
    	// write a config without any invariants / properties
    	final String noInvsCfg = "no_invs.cfg";
    	Utils.writeFile(noInvsCfg, "SPECIFICATION Spec");
    	
    	// decompose the spec into as many components as possible
    	final List<String> rawComponents = decompAll(tla, cfg);
    	final List<String> components = symbolicCompose(tla, cfg, customSymComp, rawComponents);
    	Utils.assertTrue(rawComponents.size() > 0, "Decomposition returned no components");
    	Utils.assertTrue(components.size() > 0, "Symbolic composition returned no components");
    	System.out.println("n: " + rawComponents.size());
    	System.out.println("m: " + (components.size() - 1));
    	
    	// model check the first component
    	final String firstComp = components.get(0);
		System.out.println();
		System.out.println("Component 1" + ": " + firstComp);
    	TLC tlcFirstComp = new TLC();
    	timer.reset();
    	tlcFirstComp.modelCheckOnlyGoodStates(firstComp, cfg); // TODO there's really no reason to distinguish between the 2 methods
    	System.out.println("State space gen: " + timer.timeElapsed() + "ms");
    	Utils.assertNotNull(tlcFirstComp.getLTSBuilder(), "Error generating state space for the first component!");
    	
    	// turn the first component into a safety property (interface requirement)
    	timer.reset();
    	LTS<Integer, String> ltsProp = tlcFirstComp.getLTSBuilder().toIncompleteDetAutIncludingAnErrorState();
    	System.out.println("LTS gen: " + timer.timeElapsed() + "ms");
    	System.out.println("# unique states: " + (ltsProp.size()-1) + " states");
    	int totalSumOfStatesChecked = ltsProp.size() - 1;
    	int largestProductOfStatesChecked = ltsProp.size() - 1;
    	//System.out.println();
    	//FSPWriter.INSTANCE.write(System.out, ltsProp);
    	//System.out.println();
    	
    	// minimize the LTS
    	timer.reset();
    	ltsProp = minimizeLTS(ltsProp);
    	System.out.println("minimization: " + timer.timeElapsed() + "ms");
    	System.out.println("# unique states post-minimization: " + (ltsProp.size()-1) + " states");
    	
    	// initialize the alphabet
    	AlphabetMembershipTester alphabetTester = new AlphabetMembershipTester(actionNamesInSpec(tlcFirstComp), ltsProp);
    	
    	if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
    		final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
    		System.out.println();
    		System.out.println("Total # states checked: " + totalNumStatesChecked);
    		System.out.println("Property satisfied!");
    		return;
    	}
    	if (SafetyUtils.INSTANCE.hasErrInitState(ltsProp)) {
    		final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
    		System.out.println();
    		System.out.println("Total # states checked: " + totalNumStatesChecked);
			System.out.println("Property may be violated.");
    		//FSPWriter.INSTANCE.write(System.out, ltsProp);
			return;
    	}
    	
    	// at this point, ltsProp represents the interface requirement for the 1st component.
    	// therefore, there is no need to look at the 1st component in the following loop.
    	
    	for (int i = 1; i < components.size(); ++i) {
    		final int compNum = i + 1;
    		final String comp = components.get(i);
    		System.out.println();
    		System.out.println("Component " + compNum + ": " + comp);
    		
    		TLC tlcComp = new TLC();
    		timer.reset();
        	tlcComp.modelCheck(comp, noInvsCfg, alphabetTester);
        	System.out.println("State space gen: " + timer.timeElapsed() + "ms");
        	Utils.assertNotNull(tlcComp.getLTSBuilder(), "Error generating state space for component " + compNum + "!");
        	
        	// turn the next component into an LTS (user of the interface provided by ltsProp)
        	timer.reset();
        	LTS<Integer, String> ltsComp = tlcComp.getLTSBuilder().toIncompleteDetAutWithoutAnErrorState();
        	System.out.println("LTS gen: " + timer.timeElapsed() + "ms");
        	System.out.println("# unique states: " + (ltsComp.size()-1) + " states");
        	totalSumOfStatesChecked += ltsComp.size() - 1;
        	//System.out.println();
        	//FSPWriter.INSTANCE.write(System.out, ltsComp);
        	//System.out.println();
        	
        	// minimize the LTS for the component
        	timer.reset();
        	ltsComp = minimizeLTS(ltsComp);
        	System.out.println("minimization: " + timer.timeElapsed() + "ms");
        	System.out.println("# unique states post-minimization: " + (ltsComp.size()-1) + " states");
        	largestProductOfStatesChecked = Math.max(largestProductOfStatesChecked, ltsProp.size()-1);
        	
        	// remove any actions that are now internal to ltsProp
        	// TODO this technically is an abstraction method because later components may have the action
        	// TODO this technique also gets rid of the info we need to produce counterexample traces
        	//Set<String> ltsPropAlphabet = new HashSet<>(ltsProp.getInputAlphabet());
        	//ltsPropAlphabet.removeAll(ltsComp.getInputAlphabet());
        	//ltsProp = HideUtils.INSTANCE.hideManually(ltsProp, ltsPropAlphabet);
        	
        	// create new safety property (interface requirement for all components seen so far)
    		timer.reset();
    		ltsProp = ParallelComposition.INSTANCE.parallel(ltsComp, ltsProp);
    		// TODO should we be minimizing ltsProp here now too?
    		System.out.println("New property gen (|| composition): " + timer.timeElapsed() + "ms");
        	
        	// collect the alphabet
        	alphabetTester.update(actionNamesInSpec(tlcComp), ltsProp);
    		
    		// if the new safety property is TRUE or FALSE then model checking is done
        	if (SafetyUtils.INSTANCE.ltsIsSafe(ltsProp)) {
        		final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
        		System.out.println();
        		System.out.println("Total # states checked: " + totalNumStatesChecked);
        		System.out.println("Property satisfied!");
        		return;
        	}
        	if (SafetyUtils.INSTANCE.hasErrInitState(ltsProp)) {
        		final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
        		System.out.println();
        		System.out.println("Total # states checked: " + totalNumStatesChecked);
    			System.out.println("Property may be violated.");
        		//FSPWriter.INSTANCE.write(System.out, ltsProp);
    			return;
        	}
    	}
		final int totalNumStatesChecked = Math.max(totalSumOfStatesChecked, largestProductOfStatesChecked);
		System.out.println();
		System.out.println("Total # states checked: " + totalNumStatesChecked);
		System.out.println("Property may be violated.");
		
		// encode the sequence of actions that leads to an error in a new TLA+ file
		// TODO write error trace for early termination
		writeErrorTraceFile(tla, cfg, ltsProp);
    	
    	// not unix convention, but we use this to signal to the wrapper script that
    	// it should produce an error trace
    	System.exit(99);
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
    
    public static void decompVerifyUniform(String[] args) {
    	/*
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
		*/
    }
    
    public static void toFSP(String[] args) {
    	/*
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
    	 */
    }
    
    public static void weakestAssumptionNoSink(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC("tlc");
    	tlc.modelCheck(tla, cfg);
    	
    	// error checking
    	/*
    	if (tlc.getKripke() == null) {
    		System.err.println("The spec is malformed, or the file does not exist.");
    		return;
    	}
    	System.out.println(tlc.getKripke().weakestAssumptionNoSink());
    	*/
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
    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	return tlc.stateVarsInSpec();
    }
    
    private static Set<String> actionsInSpec(final String tla, final String cfg) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	return actionsInSpec(tlc);
    }
    
    private static Set<String> actionsInSpec(final TLC tlc) {
    	final FastTool ft = (FastTool) tlc.tool;
    	return Utils.toArrayList(ft.getActions())
        		.stream()
        		.map(a -> a.getName().toString())
        		.collect(Collectors.toSet());
    }
    
    private static Set<String> actionNamesInSpec(final TLC tlc) {
    	final FastTool ft = (FastTool) tlc.tool;
    	return Utils.toArrayList(ft.getActions())
        		.stream()
        		.map(a -> a.getName().toString())
        		//.map(a -> Utils.firstLetterToLowerCase(a))
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
    		final String aSpec = "C" + iter;
    		final String bSpec = "T" + iter;
    		slice(aSpec, propertyVars, tla, cfg, true);
    		slice(bSpec, nonPropertyVars, tla, cfg, false);
        	components.add(aSpec);
        	
        	allVars = nonPropertyVars;
        	//propertyVars = calcPropertyVars(aSpec, "no_invs.cfg", bSpec, "no_invs.cfg", true);
        	propertyVars = minimalPartition(bSpec, "no_invs.cfg");
        	nonPropertyVars = Utils.setMinus(allVars, propertyVars);
        	
        	// sanity checks
        	Utils.assertTrue(allVars.equals(stateVarsInSpec(bSpec, "no_invs.cfg")), "allVars != stateVarsInSpec()");
        	Utils.assertTrue(Utils.union(propertyVars, nonPropertyVars).equals(allVars), "allVars != propertyVars \\cup nonPropertyVars");
        	Utils.assertTrue(Utils.intersection(propertyVars, nonPropertyVars).isEmpty(), "propertyVars \\cap nonPropertyVars # {}");
        	
        	tla = bSpec;
        	cfg = "no_invs.cfg";
        	++iter;
    	}
    	
    	if (iter > 1) {
    		// we decomposed into at least two components
        	components.add("T" + (iter-1));
    	}
    	else {
    		// we were not able to decompose the spec. perform monolithic MCing
    		components.add(tla);
    	}
    	return components;
    }
    
    private static Set<String> minimalPartition(final String bSpec, final String bCfg) {
    	final Set<String> bVars = stateVarsInSpec(bSpec, bCfg);
    	final Set<String> nextVarSet = Utils.setOf( Utils.chooseOne(bVars) );
    	TLC tlc = new TLC("b_" + bSpec);
    	tlc.initialize(bSpec, bCfg);
    	return tlc.stateVarsUsedInSameExprs(nextVarSet); // Fix-Point(Occurs,nextVarSet)
    }
    
    /**
     * Calculates the vars from bSpec that /may/ be needed to uphold the guarantees of the interface
     * provided in aSpec. We perform this calculation by consider all variables in bSpec that are not
     * exclusively in UNCHANGED blocks in the mutual actions of aSpec and bSpec.
     * If the parameter "minVars" is true, this method will choose the minimum vars needed to perform
     * the next slice.
     * @param aSpec
     * @param bSpec
     * @return
     */
    private static Set<String> calcPropertyVars(final String aSpec, final String aCfg, final String bSpec, final String bCfg, boolean minVars) {
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
    	final Set<String> rawPropertyVars = minVars && !varsThatMayChange.isEmpty() ?
    			Utils.setOf( Utils.chooseOne(varsThatMayChange) ) :
    			varsThatMayChange;
    	
    	// also compute all vars that occur in the same expressions as rawPropertyVars
    	final Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(rawPropertyVars);
    	return propertyVars;
    }

    /**
     * Calculates the vars from bSpec that occur as a guard in at least one action in the interface between aSpec and bSpec,
     * i.e. intersection of their alphabets.
     * @param aSpec
     * @param bSpec
     * @return
     */
    private static Set<String> calcPropertyVarsByGuards(final String aSpec, final String aCfg, final String bSpec, final String bCfg) {
    	final Set<String> aActions = actionsInSpec(aSpec, aCfg);
    	final Set<String> bActions = actionsInSpec(bSpec, bCfg);
    	final Set<String> ifaceActions = Utils.intersection(aActions, bActions);
    	
    	TLC tlc = new TLC("b_" + bSpec);
    	tlc.initialize(bSpec, bCfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// get the top level module and all op def nodes
    	final String moduleName = tlc.getModelName();
    	final ModuleNode mn = ft.getModule(moduleName);
    	final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
    			.stream()
    			.filter(m -> !m.isStandardModule())
    			.filter(m -> ifaceActions.contains(m.getName().toString()))
    			.collect(Collectors.toList());
    	
    	// find vars that are occur as a guard in at least one action in ifaceActions in bSpec
    	final Set<String> bVars = stateVarsInSpec(bSpec, bCfg);
    	final Set<String> bVarsInGuards = bVars
    			.stream()
    			.filter(v -> {
    				return moduleNodes
    						.stream()
    						.anyMatch(n -> n.varOccursInGuard(v));
    			})
    			.collect(Collectors.toSet());
    	
    	// also compute all vars that occur in the same expressions as varsThatMayChange
    	final Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(bVarsInGuards);
    	
    	return propertyVars;
    }
    
    private static void slice(final String specName, final Set<String> keepVars, final String tla, final String cfg, boolean includeInvs) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC(specName);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// calculate variables to remove from the spec
    	final Set<String> allVars = Utils.toArrayList(ft.getVarNames())
        		.stream()
        		.collect(Collectors.toSet());
    	final Set<String> removeVars = Utils.setMinus(allVars, keepVars);
    	
    	// get the invariants in the spec
		final Set<String> invariants = Utils.toArrayList(ft.getInvNames())
				.stream()
				.collect(Collectors.toSet());
    	
    	// get the top level module and all op def nodes
		final String moduleName = tlc.getModelName();
		final ModuleNode mn = ft.getModule(moduleName);
		List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
				.stream()
				// only retain module for the .tla file
				.filter(d -> moduleName.equals(d.getOriginallyDefinedInModuleNode().getName().toString()))
				.filter(d -> includeInvs ? true : !invariants.contains(d.getName().toString()))
				.collect(Collectors.toList());
		
		// decompose the module in the following steps which we repeat until fixpoint (see step 3 for termination condition):
		// 1. remove all references to the unwanted nodes in <toRemove>. mark SemanticNodes that become
		//	  bad, and hence need to be removed from the AST.
		// 2. remove any SemanticNodes that are marked as bad from step 1. this won't get rid of top level
		//    nodes that need to be removed: we handle that in step 3.
		// 3. identify top level modules (in <moduleNodes>) that need to be removed. if there are any, then
		//    add these to <toRemove> and go back to step 1.
		Set<String> toRemove = new HashSet<>(removeVars);
		boolean reachedFixpoint = false;
		while (!reachedFixpoint) {
			moduleNodes.forEach(n -> n.removeChildrenWithName(toRemove));
			moduleNodes.forEach(n -> n.removeMalformedChildren());
			final Set<String> nextToRemove = moduleNodes
					.stream()
					.filter(m -> m.isMalformed() || m.hasOnlyUnchangedConjuncts())
					.map(m -> m.getName().toString())
					.collect(Collectors.toSet());
			moduleNodes = moduleNodes
					.stream()
					.filter(m -> !nextToRemove.contains(m.getName().toString()))
					.collect(Collectors.toList());
			reachedFixpoint = toRemove.containsAll(nextToRemove);
			toRemove.addAll(nextToRemove);
		}
		moduleNodes.forEach(n -> n.removeUnusedLetDefs());
		moduleNodes.forEach(n -> n.removeConjunctsWithEmptyUnchangedOp());
		
		// create TLA+ from the node defs
		final String specBody = moduleNodes
				.stream()
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
