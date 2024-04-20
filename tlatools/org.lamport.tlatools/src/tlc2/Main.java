package tlc2;

import recomp.RecompVerify;

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
    	if (args.length >= 2) {
    		final String tla = args[0];
    		final String cfg = args[1];
    		final boolean verbose = hasFlag(args, "--verbose");
    		final boolean custom = hasFlag(args, "--cust");
    		final boolean naive = hasFlag(args, "--naive");
    		//final boolean heuristic = !custom && !naive;
    		final String recompFile = custom ? positionalArg(args, "--cust") : "";
    		
    		// TODO ian this is lazy
    		Utils.assertTrue(!custom || !recompFile.isEmpty(), "--cust must be followed by a recomp file!");
    		Utils.assertTrue(!(custom && naive), "--custom and --naive are mutually exclusive options!");
    		
    		final String recompStrategy = custom ? "CUSTOM" : naive ? "NAIVE" : "HEURISTIC";
    		RecompVerify.recompVerify(tla, cfg, recompStrategy, recompFile, verbose);
    	}
    	
    	// invalid args, display usage
    	else {
    		System.out.println("usage: recomp-verify <spec> <cfg> [--naive] [--cust <recomp-file>] [--verbose]\n"
    				+ "* --naive and --cust are mutually exclusive");
    	}
    }
    
    private static boolean hasFlag(String[] args, final String flag) {
    	return Utils.toArrayList(args)
				.stream()
				.filter(s -> s.equals(flag))
				.count() > 0;
    }
    
    private static String positionalArg(String[] args, final String param) {
    	int paramIdx = -1;
    	for (int i = 0; i < args.length; ++i) {
    		if (param.endsWith(args[i])) {
    			// the positional arg is right after the param flag
    			paramIdx = i + 1;
    		}
    	}
    	Utils.assertTrue(paramIdx >= 0 && paramIdx < args.length, "Invalid use of the param flag: " + param);
    	return args[paramIdx];
    }
}
