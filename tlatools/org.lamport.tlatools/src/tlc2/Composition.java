package tlc2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.ExtKripke;
import tlc2.tool.impl.FastTool;

public class Composition {
    
    public static void toFSP(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC("tlc");
    	TLC.runTLC(tla, cfg, tlc);
    	
    	// error checking
    	if (tlc.getKripke() == null) {
    		System.err.println("The spec is malformed, or the file does not exist.");
    		return;
    	}
    	System.out.println(tlc.getKripke().toFSP());
    }
    
    public static void weakestAssumption(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC("tlc");
    	TLC.runTLC(tla, cfg, tlc);
    	
    	// error checking
    	if (tlc.getKripke() == null) {
    		System.err.println("The spec is malformed, or the file does not exist.");
    		return;
    	}
    	System.out.println(tlc.getKripke().weakestAssumption());
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
    	
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("init");
    	tlc.initialize(tla, cfg);
    	
    	// get state vars to decompose with
    	Set<String> allVars = stateVarsInSpec(tla, cfg);
    	Set<String> propertyVars = tlc.stateVariablesUsedInInvariants();
    	Set<String> nonPropertyVars = Utils.setMinus(allVars, propertyVars);
    	
    	int iter = 1;
    	while (propertyVars.size() > 0 && nonPropertyVars.size() > 0) {
    		final String aSpec = "A" + iter;
    		final String bSpec = "B" + iter;
    		decompose(aSpec, propertyVars, tla, cfg, true);
        	decompose(bSpec, nonPropertyVars, tla, cfg, false);
        	
        	allVars = stateVarsInSpec(bSpec, "no_invs.cfg");
        	propertyVars = calcPropertyVars(aSpec, "no_invs.cfg", bSpec, "no_invs.cfg");
        	nonPropertyVars = Utils.setMinus(allVars, propertyVars);
        	tla = bSpec;
        	cfg = "no_invs.cfg";
        	++iter;
    	}
    }
    
    private static Set<String> stateVarsInSpec(final String tla, final String cfg) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("sv_" + tla);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	return Utils.toArrayList(ft.getVarNames())
        		.stream()
        		.collect(Collectors.toSet());
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
    	return varsThatMayChange;
    }
    
    private static void decompose(final String specName, final Set<String> keepVars, final String tla, final String cfg, boolean includeInvs) {
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC(specName);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// calculate variables to remove from the spec
    	final Set<String> allVars = Utils.toArrayList(ft.getVarNames())
        		.stream()
        		.collect(Collectors.toSet());
    	final Set<String> removeVars = Utils.setMinus(allVars, keepVars);
    	
    	// get the actions and invariants in the spec
		final Set<String> actionNames = Utils.toArrayList(ft.getActions())
				.stream()
				.map(a -> a.getName().toString())
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

    // code for accessing the init state!
	// decompose init state based on state vars in propertyVars
	//Utils.assertTrue(ft.getInitStateSpec().size() == 1, "There should be exactly one init state predicate!");
	//final Action initAct = ft.getInitStateSpec().elementAt(0);
	//initAct.getOpDef().removeConjunctsWithoutStateVars(propertyVars);
}
