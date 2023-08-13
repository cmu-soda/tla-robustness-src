package tlc2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpDefNode;
import tlc2.RobustDiffRep.SpecScope;
import tlc2.tool.Action;
import tlc2.tool.EKState;
import tlc2.tool.ExtKripke;
import tlc2.Utils.Pair;
import tlc2.tool.impl.FastTool;

public class Robustness {

	private static final boolean GROUP_DIFF_REP_BY_ACTION = true;
	
	private static final String COMPARISON_TYPE = "comparison_type";
	private static final String SPEC_TO_PROPERTY = "spec_to_property";
	private static final String SPEC_TO_ENV = "spec_to_env";
	private static final String SPEC_TO_SPEC = "spec_to_spec";
	
	private static final String SPEC_NAME = "spec_name";
	private static final String SPEC1_NAME = "spec1_name";
	private static final String SPEC2_NAME = "spec2_name";
	
	private static final String COMBINED_ERR_PRE_TLA = "combined_err_pre_tla";
	private static final String COMBINED_ERR_POST_TLA = "combined_err_post_tla";
	private static final String SPEC1_SAT_SPEC2_CFG = "spec1_sat_spec2_cfg";
	private static final String SPEC2_SAT_SPEC1_CFG = "spec2_sat_spec1_cfg";
	
	private static final String SPEC_IS_SAFE = "spec_is_safe";
	private static final String CLOSED_SYSTEM_IS_SAFE = "closed_system_is_safe";
	private static final String SPEC1_IS_SAFE = "spec1_is_safe";
	private static final String SPEC2_IS_SAFE = "spec2_is_safe";
	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	private static final String DIFF_REP_STATE_FORMULA_ERROR = "diff_rep_state_formula_error";
	private static final String MISSING_TYPEOK = "missing_typeok";
	private static final String MISSING_BOTH_TYPEOKS = "missing_both_typeoks";
	private static final String TYPE_OK = "TypeOK";
	private static final String ALL = "All";
    
    // M_err_rep: states that are in (M_err \cap P) but MAY leave P in one step
    public static void compareSpecToProperty(String[] args, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String outputLoc = args[1] + "/";
    	final String tla = args[2];
    	final String cfg = args[3];
    	
    	// initialize and run TLC
    	TLC tlc = new TLC("cmp");
    	tlc.modelCheck(tla, cfg);
    	
    	// error checking
    	if (tlc.getKripke() == null) {
    		System.err.println("The spec is malformed.");
    		return;
    	}

    	jsonStrs.put(COMPARISON_TYPE, SPEC_TO_PROPERTY);
    	jsonStrs.put(SPEC_NAME, tlc.getSpecName());
    	
    	// compute the representation for beh(P) - \eta(spec,P)
    	computePropertyDiffRep(tla, tlc, tlc.getKripke(), outputLoc, jsonStrs, jsonLists);
    }

	// M_err_rep: states that are in (M_err \cap E) but MAY leave E in one step
    public static void compareSpecToEnvironment(String[] args, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String outputLoc = args[1] + "/";
    	final String tlaM = args[2];
    	final String cfgM = args[3];
    	final String tlaClosed = args[4];
    	final String cfgClosed = args[5];
    	assert(!tlaM.equals(tlaClosed));
    	
    	// run TLC for M and the closed system
    	TLC tlcM = new TLC("M");
    	TLC tlcClosed = new TLC("closed");
    	tlcM.modelCheck(tlaM, cfgM);
    	tlcClosed.modelCheck(tlaClosed, cfgClosed);
    	final ExtKripke kripkeM = tlcM.getKripke();
    	final ExtKripke kripkeClosed = tlcClosed.getKripke();
    	
    	// error checking
    	if (kripkeM == null) {
    		System.err.println("The spec is malformed.");
    		return;
    	}
    	if (kripkeClosed == null) {
    		System.err.println("The closed system spec is malformed.");
    		return;
    	}
    	
    	final ExtKripke kripkeCmp = new ExtKripke(kripkeM, kripkeClosed);
    	computeEnvDiffRep(tlaM, tlcM, kripkeCmp, outputLoc, jsonStrs, jsonLists);
    	
    	jsonStrs.put(COMPARISON_TYPE, SPEC_TO_ENV);
    	jsonStrs.put(SPEC_NAME, tlcM.getSpecName());
    	jsonStrs.put(SPEC_IS_SAFE, tlcM.getKripke().isSafe() ? TRUE : FALSE);
    	jsonStrs.put(CLOSED_SYSTEM_IS_SAFE, tlcClosed.getKripke().isSafe() ? TRUE : FALSE);
    }
    
    public static void compareSpecs(String[] args, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String outputLoc = args[1] + "/";
    	final String tla1 = args[2];
    	final String cfg1 = args[3];
    	final String tla2 = args[4];
    	final String cfg2 = args[5];
    	assert(!tla1.equals(tla2));
    	
    	// initialize and run TLC
    	TLC tlc1 = new TLC("spec1");
    	TLC tlc2 = new TLC("spec2");
    	tlc1.modelCheck(tla1, cfg1);
    	tlc2.modelCheck(tla2, cfg2);

    	// error checking
    	Utils.assertNotNull(tlc1.getKripke(), "The first spec is malformed.");
    	Utils.assertNotNull(tlc2.getKripke(), "The second spec is malformed.");
    	
    	jsonStrs.put(COMPARISON_TYPE, SPEC_TO_SPEC);
    	jsonStrs.put(SPEC1_NAME, tlc1.getSpecName());
    	jsonStrs.put(SPEC2_NAME, tlc2.getSpecName());
    	jsonStrs.put(SPEC1_IS_SAFE, tlc1.getKripke().isSafe() ? TRUE : FALSE);
    	jsonStrs.put(SPEC2_IS_SAFE, tlc2.getKripke().isSafe() ? TRUE : FALSE);
    	
    	// create err pre/post TLA+ specs
    	createErrPre(tlc1, tlc2, tla1, tla2, cfg1, cfg2, outputLoc, jsonStrs);
    	createErrPost(tlc1, tlc2, tla1, tla2, cfg1, cfg2, outputLoc, jsonStrs);
    	
    	// create the cfgs for comparing the pre/post specs
    	final String spec1SatSpec2Cfg = specSatConfig("Spec1", "Spec2", outputLoc);
    	final String spec2SatSpec1Cfg = specSatConfig("Spec2", "Spec1", outputLoc);
    	jsonStrs.put(SPEC1_SAT_SPEC2_CFG, spec1SatSpec2Cfg);
    	jsonStrs.put(SPEC2_SAT_SPEC1_CFG, spec2SatSpec1Cfg);
    	
    	// compute the representation for \eta(spec2,P) - \eta(spec1,P)
    	// and \eta(spec1,P) - \eta(spec2,P)
    	computeComparisonDiffRep(tlc1, tlc2, outputLoc, jsonStrs, jsonLists);
    }
    
    private static void computePropertyDiffRep(final String tlaFile, final TLC tlc, final ExtKripke kripke, final String outputLoc,
    		Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	computeSpecDiffRep(tlaFile, tlc, kripke, outputLoc, kripke.safetyBoundaryPerAction(), jsonStrs, jsonLists);
    }
    
    private static void computeEnvDiffRep(final String tlaFile, final TLC tlc, final ExtKripke kripke, final String outputLoc,
    		Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	computeSpecDiffRep(tlaFile, tlc, kripke, outputLoc, kripke.robustSafetyBoundaryPerAction(), jsonStrs, jsonLists);
    }
    
    private static void computeSpecDiffRep(final String tlaFile, final TLC tlc, final ExtKripke kripke, final String outputLoc,
    		final Map<String, Set<EKState>> safetyBoundaryByGroup,
    		Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	jsonStrs.put(SPEC_IS_SAFE, kripke.isSafe() ? TRUE : FALSE);
    	
    	// create diffRep before the 'if' to make sure we write whether the safetyBoundary is empty or not
    	final Set<EKState> safetyBoundary = kripke.safetyBoundary();
    	RobustDiffRep diffRep = new RobustDiffRep(tlc.getSpecName(), SpecScope.Spec, outputLoc, safetyBoundary, safetyBoundaryByGroup, jsonStrs, jsonLists);
    	
    	if (!kripke.isSafe()) {
        	diffRep.writeBoundary();
        	
        	// a TypeOK is required to gather the info we need to create a sep.fol file
        	if (tlc.hasInvariant(TYPE_OK)) {
            	// compute the entire state space
            	final TLC tlcTypeOK = new TLC("PropDiffRepTypeOK");
            	runTLCExtractStateSpace(tlaFile, tlc, outputLoc, tlcTypeOK);
            	Utils.assertNotNull(tlcTypeOK.getKripke(), "Unable to build state space from TypeOK!");
            	diffRep.writeBoundaryFOLSeparatorFile(tlcTypeOK);
        	}
        	else {
            	jsonStrs.put(DIFF_REP_STATE_FORMULA_ERROR, MISSING_TYPEOK);
        	}
    	}
    }
    
    private static void computeComparisonDiffRep(final TLC tlc1, final TLC tlc2, final String outputLoc, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final ExtKripke kripke1 = tlc1.getKripke();
    	final ExtKripke kripke2 = tlc2.getKripke();
    	final ExtKripke errPre1 = kripke1.createErrPre();
    	final ExtKripke errPre2 = kripke2.createErrPre();
    	final ExtKripke errPost1 = kripke1.createErrPost();
    	final ExtKripke errPost2 = kripke2.createErrPost();

    	jsonStrs.put(SPEC1_IS_SAFE, kripke1.isSafe() ? TRUE : FALSE);
    	jsonStrs.put(SPEC2_IS_SAFE, kripke2.isSafe() ? TRUE : FALSE);
    	
    	if (!kripke1.isSafe() && !kripke2.isSafe()) {
    		// compute \eta1-\eta2 and \eta2-\eta1
    		computeComparisonDiffRepWrtOneSpec(new ExtKripke(kripke2), new ExtKripke(errPre2), new ExtKripke(errPost2), new ExtKripke(errPre1), new ExtKripke(errPost1),
    				tlc2, tlc1, tlc1.getSpecName(), outputLoc, SpecScope.Spec1, jsonStrs, jsonLists);
    		computeComparisonDiffRepWrtOneSpec(new ExtKripke(kripke1), new ExtKripke(errPre1), new ExtKripke(errPost1), new ExtKripke(errPre2), new ExtKripke(errPost2),
    				tlc1, tlc2, tlc2.getSpecName(), outputLoc, SpecScope.Spec2, jsonStrs, jsonLists);
    	}
    }

	// compute the diff rep, i.e. the states that represent \eta2 - \eta1
    private static void computeComparisonDiffRepWrtOneSpec(final ExtKripke refKripke,
    		final ExtKripke errPre1, final ExtKripke errPost1, final ExtKripke errPre2, final ExtKripke errPost2,
    		final TLC tlc1, final TLC tlc2, final String refSpec, final String outputLoc,
    		final SpecScope specScope, Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final Set<Pair<EKState,String>> diffRepSet = Utils.union(
    			ExtKripke.behaviorDifferenceRepresentation(errPre1, errPre2, refKripke),
    			ExtKripke.behaviorDifferenceRepresentation(errPost1, errPost2, refKripke));
    	final Set<EKState> diffRepStates = Utils.projectFirst(diffRepSet);
    	final Map<String, Set<EKState>> diffRepStatesByGroup = groupTheDiffRep(diffRepSet, GROUP_DIFF_REP_BY_ACTION);

    	// create diffRep before the 'if' to make sure we write whether the safetyBoundary is empty or not
    	RobustDiffRep diffRep = new RobustDiffRep(refSpec, specScope, outputLoc, diffRepStates, diffRepStatesByGroup, jsonStrs, jsonLists);
    	
    	if (diffRepSet.size() > 0) {
        	// the two specs have overlapping error traces / state space so we compare them
        	diffRep.writeBoundary();

        	// a TypeOK is required to gather the info we need to create a sep.fol file
        	final boolean bothHaveTypeOK = tlc1.hasInvariant(TYPE_OK) && tlc2.hasInvariant(TYPE_OK);
        	if (bothHaveTypeOK) {
            	// compute the entire state space
            	final TLC tlcTypeOK = new TLC("CmpTypeOK" + refSpec);
            	runTLCExtractStateSpace(tlc1, tlc2, outputLoc, tlcTypeOK);
            	diffRep.writeBoundaryFOLSeparatorFile(tlcTypeOK);
        	}
        	else {
            	jsonStrs.put(DIFF_REP_STATE_FORMULA_ERROR, MISSING_BOTH_TYPEOKS);
        	}
    	}
    }
    
    private static Map<String, Set<EKState>> groupTheDiffRep(final Set<Pair<EKState,String>> diffRepSet, final boolean groupByAction) {
    	if (groupByAction) {
    		Map<String, Set<EKState>> diffRepGroups = new HashMap<>();
    		for (final Pair<EKState,String> diffRep : diffRepSet) {
    			final String group = diffRep.second;
    			final EKState state = diffRep.first;
    			if (!diffRepGroups.containsKey(group)) {
    				diffRepGroups.put(group, new HashSet<>());
    			}
    			diffRepGroups.get(group).add(state);
    		}
    		return diffRepGroups;
    	}
    	else {
        	final Set<EKState> diffRepStates = Utils.projectFirst(diffRepSet);
			Map<String, Set<EKState>> singleton = new HashMap<>();
			singleton.put(ALL, diffRepStates);
			return singleton;
    	}
    }
	
    private static void createErrPre(final TLC tlc1, final TLC tlc2, final String tla1, final String tla2, final String cfg1, final String cfg2,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	// collect state variables from each spec
    	Set<String> vars1 = new HashSet<String>();
    	Set<String> vars2 = new HashSet<String>();
    	
    	// create one err pre file for each spec, then combine them into a single one for comparison
    	final String tag = "ErrPre";
    	final String specName1 = createErrPre(tag, tlc1, tla1, cfg1, vars1, outputLoc, jsonOutput);
    	final String specName2 = createErrPre(tag, tlc2, tla2, cfg2, vars2, outputLoc, jsonOutput);
    	final String combineSpecName = combineSpecTLA(tag, specName1, specName2, vars1, vars2, outputLoc);
        jsonOutput.put(COMBINED_ERR_PRE_TLA, combineSpecName);
    }
    
    private static String createErrPre(final String tag, final TLC tlc, final String tla, final String cfg, Set<String> vars,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	ExtKripke kripke = tlc.getKripke();
    	ExtKripke errPreKripke = kripke.createErrPre();
    	final boolean strongFairness = true; // need SF in err pre
    	return kripkeToTLA(tag, tlc, errPreKripke, tla, cfg, outputLoc, strongFairness, vars);
    }
    
    private static void createErrPost(final TLC tlc1, final TLC tlc2, final String tla1, final String tla2, final String cfg1, final String cfg2,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	// collect state variables from each spec
    	Set<String> vars1 = new HashSet<String>();
    	Set<String> vars2 = new HashSet<String>();
    	
    	// create one err pre file for each spec, then combine them into a single one for comparison
    	final String tag = "ErrPost";
    	final String specName1 = createErrPost(tag, tlc1, tla1, cfg1, vars1, outputLoc, jsonOutput);
    	final String specName2 = createErrPost(tag, tlc2, tla2, cfg2, vars2, outputLoc, jsonOutput);
    	final String combineSpecName = combineSpecTLA(tag, specName1, specName2, vars1, vars2, outputLoc);
        jsonOutput.put(COMBINED_ERR_POST_TLA, combineSpecName);
    }
    
    private static String createErrPost(final String tag, final TLC tlc, final String tla, final String cfg, Set<String> vars,
    		final String outputLoc, Map<String,String> jsonOutput) {
    	ExtKripke kripke = tlc.getKripke();
    	ExtKripke errPostKripke = kripke.createErrPost();
    	final boolean strongFairness = false; // do not add SF to err post
    	return kripkeToTLA(tag, tlc, errPostKripke, tla, cfg, outputLoc, strongFairness, vars);
    }
    
    private static String combineSpecTLA(final String tag, final String specName1, final String specName2, final Set<String> vars1, final Set<String> vars2, final String outputLoc) {
        final String specName = "Combined_" + tag;
        final String varsSeqName = "vars_" + tag;
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        ArrayList<String> varNameList1 = Utils.toArrayList(vars1);
        ArrayList<String> varNameList2 = Utils.toArrayList(vars2);
        
        vars1.addAll(vars2);
        ArrayList<String> combineVarNameList = Utils.toArrayList(vars1);
        
        final String varList = String.join(", ", combineVarNameList);
        final String varsDecl = "VARIABLES " + varList;
        
        final String spec1 = "S1 == INSTANCE " + specName1 + " WITH " + Utils.instanceWithList(varNameList1);
        final String spec2 = "S2 == INSTANCE " + specName2 + " WITH " + Utils.instanceWithList(varNameList2);
        final String spec1Def = "Spec1 == S1!Spec"; // TODO implicit assumption that spec defs will be called Spec
        final String spec2Def = "Spec2 == S2!Spec";

        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(spec1).append("\n");
        builder.append("\n");
        builder.append(spec2).append("\n");
        builder.append("\n");
        builder.append(spec1Def).append("\n");
        builder.append(spec2Def).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");
        
        final String name = outputLoc + specName + ".tla";
        Utils.writeFile(name, builder.toString());
        
        return name;
    }
    
    private static String stateSpaceTLA(final String specName, final TLC tlc1, final TLC tlc2, final String outputLoc) {
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";
        
        FastTool ft1 = (FastTool) tlc1.tool;
        FastTool ft2 = (FastTool) tlc2.tool;
        ArrayList<String> varNameList1 = Utils.toArrayList(ft1.getVarNames());
        ArrayList<String> varNameList2 = Utils.toArrayList(ft2.getVarNames());
        Set<String> combineVarNames = new HashSet<String>();
        combineVarNames.addAll(varNameList1);
        combineVarNames.addAll(varNameList2);
        
        final String varList = String.join(", ", combineVarNames);
        final String varsDecl = "VARIABLES " + varList;
        
        final String specName1 = tlc1.getSpecName();
        final String specName2 = tlc2.getSpecName();
        final String spec1 = "S1 == INSTANCE " + specName1 + " WITH " + Utils.instanceWithList(varNameList1);
        final String spec2 = "S2 == INSTANCE " + specName2 + " WITH " + Utils.instanceWithList(varNameList2);
        final String typeOKDef = "TypeOK == S1!TypeOK /\\ S2!TypeOK";
        
        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(spec1).append("\n");
        builder.append(spec2).append("\n");
        builder.append(typeOKDef).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");
        
        final String file = outputLoc + specName + ".tla";
        Utils.writeFile(file, builder.toString());
        
        return file;
    }
    
    private static String kripkeToTLA(final String tag, final TLC tlc, final ExtKripke kripke,
    		final String tla, final String cfg, final String outputLoc, final boolean strongFairness, Set<String> vars) {
        FastTool ft = (FastTool) tlc.tool;
        
        final String specName = tlc.getSpecName() + "_" + tag;
        final String varsSeqName = "vars";
        final String specDecl = "--------------------------- MODULE " + specName + " ---------------------------";
        final String endModule = "=============================================================================";

        final List<String> moduleWhiteList =
        		Arrays.asList("Bags", "FiniteSets", "Functions", "Integers", "Json", "Naturals",
        				"NaturalsInduction", "RealTime", "Sequences", "SequencesExt", "TLC", "TLCExt");
        ArrayList<String> moduleNameList = Utils.filterArrayWhiteList(moduleWhiteList, ft.getModuleNames());
        ArrayList<String> varNameList = Utils.toArrayList(ft.getVarNames());
        vars.addAll(varNameList);

        final String moduleList = String.join(", ", moduleNameList);
        final String varList = String.join(", ", varNameList);
        final String modulesDecl = moduleList.isEmpty() ? "" : "EXTENDS " + moduleList;
        final String varsDecl = "VARIABLES " + varList;
        final String varsSeq = varsSeqName + " == <<" + varList + ">>";
        final String specFairness = fairnessConditionString(tla, tlc);

        StringBuilder builder = new StringBuilder();
        builder.append(specDecl).append("\n");
        builder.append(modulesDecl).append("\n");
        builder.append("\n");
        builder.append(varsDecl).append("\n");
        builder.append("\n");
        builder.append(varsSeq).append("\n");
        builder.append("\n");
        builder.append(kripke.toPartialTLASpec(varsSeqName, specFairness, strongFairness)).append("\n");
        builder.append(endModule).append("\n");
        builder.append("\n");

        final String fileName = specName + ".tla";
        final String file = outputLoc + fileName;
        Utils.writeFile(file, builder.toString());
        
        return specName;
    }
    
    private static String fairnessConditionString(final String tla, final TLC tlc) {
        Action[] fairnessConditions = tlc.tool.getTemporals();
        List<String> fairnessConditionStrs = new ArrayList<>();
        for (Action condition : fairnessConditions) {
        	final String condStr = Utils.extractSyntaxFromSource(tla, condition.getLocation());
        	fairnessConditionStrs.add(condStr);
        }
        return String.join(" /\\ ", fairnessConditionStrs);
    }
    
    private static String specSatConfig(final String spec1, final String spec2, final String outputLoc) {
        StringBuilder builder = new StringBuilder();
        builder.append("SPECIFICATION ").append(spec1).append("\n");
        builder.append("PROPERTY ").append(spec2);
        final String file = outputLoc + spec1 + "Sat" + spec2 + ".cfg";
        Utils.writeFile(file, builder.toString());
        return file;
    }
    
    private static String stateSpaceConfig(final String specName, final String outputLoc) {
        StringBuilder builder = new StringBuilder();
        builder.append("SPECIFICATION TypeOK");
        
        final String file = outputLoc + specName + ".cfg";
        Utils.writeFile(file, builder.toString());
        
        return file;
    }
    
    private static void runTLCExtractStateSpace(final String tlaFile, final TLC tlc, final String outputLoc, TLC tlcTypeOK) {
    	// no need to create a new TLA file since we've already checked (in the caller to this function)
    	// that there is a TypeOK in tlaFile
        final String cfgName = "JustTypeOK";
        final String cfgFile = stateSpaceConfig(cfgName, outputLoc);
        tlcTypeOK.modelCheck(tlaFile, cfgFile);
    }
    
    private static void runTLCExtractStateSpace(final TLC tlc1, final TLC tlc2, final String outputLoc, TLC tlcTypeOK) {
        final String specName = "CombinedTypeOK";
        final String tlaFile = stateSpaceTLA(specName, tlc1, tlc2, outputLoc);
        final String cfgFile = stateSpaceConfig(specName, outputLoc);
        tlcTypeOK.modelCheck(tlaFile, cfgFile);
    }
}
