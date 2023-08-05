package tlc2;

import java.util.HashSet;
import java.util.Set;

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
    

    public static void decomposeWith(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("tlc");
    	tlc.initialize(tla, cfg);
    	
    	final Set<String> propertyVars = tlc.stateVariablesUsedInInvariants();
    	
    	final FastTool ft = (FastTool) tlc.tool;
    	Set<String> actNames = new HashSet<>();
		for (final Action act : ft.getActions()) {
			final String actName = act.getName().toString();
			if (!actNames.contains(actName)) {
				actNames.add(actName);
				final OpDefNode opNode = act.getOpDef();
				
				opNode.removeConjunctsWithoutStateVars(propertyVars);
				
				if (!opNode.hasOnlyUnchangedConjuncts()) {
					final String str = opNode.toTLA(true);
					final String indented = str.replace("\n", "\n  ");
					System.out.println(indented);
					System.out.println();
				}
			}
		}
    }
    
    public static void decomposeWithout(String[] args) {
    	final String tla = args[1];
    	final String cfg = args[2];
    	
    	// initialize TLC, DO NOT run it though
    	TLC tlc = new TLC("tlc");
    	tlc.initialize(tla, cfg);
    	
    	final Set<String> propertyVars = tlc.stateVariablesUsedInInvariants();
    	
    	final FastTool ft = (FastTool) tlc.tool;
    	Set<String> actNames = new HashSet<>();
		for (final Action act : ft.getActions()) {
			final String actName = act.getName().toString();
			if (!actNames.contains(actName)) {
				actNames.add(actName);
				final OpDefNode opNode = act.getOpDef();
				
				opNode.removeConjunctsWithStateVars(propertyVars);
				
				if (!opNode.hasOnlyUnchangedConjuncts()) {
					final String str = opNode.toTLA(true);
					final String indented = str.replace("\n", "\n  ");
					System.out.println(indented);
					System.out.println();
				}
			}
		}
    }
}
