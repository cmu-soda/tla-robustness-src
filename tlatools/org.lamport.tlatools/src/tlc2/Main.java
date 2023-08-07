package tlc2;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class Main {
    public static void main(String[] args) throws Exception {
    	try {
    		calc(args);
    	}
    	catch (Exception e) {
    		e.printStackTrace();
    	}
    	finally {
    		System.exit(0);
    	}
    }
    
    public static void calc(String[] args) {
    	Map<String,String> jsonStrs = new HashMap<>();
    	Map<String,List<String>> jsonLists = new HashMap<>();
    	
    	// robustness functionality
    	// TODO add functionality for compareSpecToEnvironment
    	if (args.length == 4 && args[0].equals("--prop")) {
    		Robustness.compareSpecToProperty(args, jsonStrs, jsonLists);
        	System.out.println(Utils.asJson(jsonStrs, jsonLists));
    	}
    	else if (args.length == 6 && args[0].equals("--env")) {
    		Robustness.compareSpecToEnvironment(args, jsonStrs, jsonLists);
        	System.out.println(Utils.asJson(jsonStrs, jsonLists));
    	}
    	else if (args.length == 6 && args[0].equals("--cmp")) {
    		Robustness.compareSpecs(args, jsonStrs, jsonLists);
        	System.out.println(Utils.asJson(jsonStrs, jsonLists));
    	}
    	
    	// convert a TLA+ spec to FSP
    	else if (args.length == 3 && args[0].equals("--to-fsp")) {
    		Composition.toFSP(args);
    	}
    	
    	// compose two TLA+ specs
    	else if (args.length == 5 && args[0].equals("--compose")) {
    		System.out.println(Composition.composeSpecs(args));
    	}
    	
    	// decompose a TLA+ spec into two, WIP
    	else if (args.length == 3 && args[0].equals("--decomp")) {
        	Composition.decompose(args);
    	}
    	
    	// invalid args, display usage
    	else {
    		System.out.println("usage: tlc-ian <flag> <output_loc> <spec1> <cfg1> [<spec2> <cfg2>]\nflag=--prop|--env|--cmp");
    	}
    }
}
