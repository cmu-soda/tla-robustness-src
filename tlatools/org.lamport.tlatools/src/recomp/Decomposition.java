package recomp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.impl.FastTool;

public class Decomposition {
    
	/**
	 * Decompose a monolithic specification into granular components
	 * @param tla
	 * @param cfg
	 * @return
	 */
    public static List<String> decompAll(String tla, String cfg) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	
    	// get state vars to decompose with
    	Set<String> invariantVars = tlc.stateVariablesUsedInInvariants();
    	Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(invariantVars);
    	Set<String> allVars = tlc.stateVarsInSpec();
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
        	Utils.assertTrue(allVars.equals(TLC.stateVarsInSpec(bSpec, "no_invs.cfg")), "allVars != stateVarsInSpec()");
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
    	final Set<String> bVars = TLC.stateVarsInSpec(bSpec, bCfg);
    	final Set<String> nextVarSet = Utils.setOf( Utils.chooseOne(bVars) );
    	TLC tlc = new TLC("b_" + bSpec);
    	tlc.initialize(bSpec, bCfg);
    	return tlc.stateVarsUsedInSameExprs(nextVarSet); // Fix-Point(Occurs,nextVarSet)
    }
    
    /**
     * Simulates recomposition by decomposing the monolithic specification into the components specified by the
     * recomposition map (<componentGroupings>)
     * @param tla
     * @param cfg
     * @param componentGroupings
     * @param allComponents
     * @return
     */
    public static List<String> decompForSymbolicCompose(String tla, String cfg, final List<List<String>> componentGroupings, boolean allComponents) {
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

        	final Set<String> allVars = TLC.stateVarsInSpec(tla, cfg);
        	final Set<String> propertyVars = componentGroupings.get(i)
        			.stream()
        			.map(c -> TLC.stateVarsInSpec(c, "no_invs.cfg"))
        			.reduce((Set<String>) new HashSet<String>(),
        					(acc, s) -> Utils.union(acc, s),
        					(s, t) -> Utils.union(s, t));
        	final Set<String> nonPropertyVars = Utils.setMinus(allVars, propertyVars);
    		
    		slice(aSpec, propertyVars, tla, cfg, true);
    		slice(bSpec, nonPropertyVars, tla, cfg, false);
        	components.add(aSpec);
        	
        	final List<String> group = componentGroupings.get(i);
        	final String composedStr = String.join(" || ", group);
			System.out.println(aSpec + " = " + composedStr);
			
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
    			System.out.println(name + finalIter + " = " + composedStr);
    		}
    	}
    	else {
    		// we were not able to decompose the spec. perform monolithic MCing
    		components.add(tla);
    	}
    	return components;
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
}
