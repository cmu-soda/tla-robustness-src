package tlc2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.tool.Action;
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
    
    public static String composeSpecs(String[] args) {
		final String tla1 = args[1];
		final String cfg1 = args[2];
		final String tla2 = args[3];
		final String cfg2 = args[4];
		return ExtKripke.composeSpecs(tla1, cfg1, tla2, cfg2);
    }


    public static void decompose(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("tlc");
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// get state vars to decompose with
        final Set<String> allVars = Utils.toArrayList(ft.getVarNames())
        		.stream()
        		.collect(Collectors.toSet());
    	final Set<String> propertyVars = tlc.stateVariablesUsedInInvariants();
    	final Set<String> nonPropertyVars = Utils.setMinus(allVars, propertyVars);
    	
    	decompose("A", allVars, propertyVars, tla, cfg, true);
    	decompose("B", allVars, nonPropertyVars, tla, cfg, false);
    }
    
    public static void decompose(final String specName, final Set<String> allVars, final Set<String> keepVars, final String tla, final String cfg, boolean includeInvs) {
    	final Set<String> removeVars = Utils.setMinus(allVars, keepVars);
    	
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC(specName);
    	tlc.initialize(tla, cfg);
    	final FastTool ft = (FastTool) tlc.tool;
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
