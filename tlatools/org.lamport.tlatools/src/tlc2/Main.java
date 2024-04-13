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
    	
    	// invoke the Decomposition Verify algorithm to perform MC with a custom re-mapping
    	else if (args.length >= 4 && args[0].equals("--verif") && args[3].equals("--sc")) {
    		final boolean verbose = args.length == 5 && args[4].equals("--verbose");
        	Composition.decompVerify(args, "CUSTOM", verbose);
    	}
    	
    	// invoke the Decomposition Verify algorithm to perform MC with the naive re-mapping
    	else if (args.length >= 4 && args[0].equals("--verif") && args[3].equals("--naive")) {
    		final boolean verbose = args.length == 5 && args[4].equals("--verbose");
        	Composition.decompVerify(args, "NAIVE", verbose);
    	}
    	
    	// invoke the Decomposition Verify algorithm to perform MC using the heuristic for the re-mapping
    	else if (args.length >= 3 && args[0].equals("--verif")) {
    		final boolean verbose = args.length == 4 && args[3].equals("--verbose");
        	Composition.decompVerify(args, "HEURISTIC", verbose);
    	}
    	
    	// invoke naive version of the Decomposition Verify algorithm to perform MC
    	else if (args.length == 3 && args[0].equals("--verif-unif")) {
        	Composition.decompVerifyUniform(args);
    	}
    	
    	// convert a TLA+ spec to FSP
    	else if (args.length == 3 && args[0].equals("--to-fsp")) {
    		Composition.toFSP(args);
    	}
    	
    	// generate the weakest assumption for the spec
    	else if (args.length == 3 && args[0].equals("--wa")) {
    		Composition.weakestAssumptionNoSink(args);
    	}
    	
    	// compose two TLA+ specs
    	else if (args.length == 5 && args[0].equals("--compose")) {
    		System.out.println(Composition.composeSpecs(args));
    	}
    	
    	// decompose a TLA+ spec into two
    	else if (args.length == 3 && args[0].equals("--decomp")) {
        	Composition.decompose(args);
    	}
    	
    	// invalid args, display usage
    	else {
    		System.out.println("usage: tlc-ian <flag> <output_loc> <spec1> <cfg1> [<spec2> <cfg2>]\nflag=--prop|--env|--cmp");
    	}
    }
}
