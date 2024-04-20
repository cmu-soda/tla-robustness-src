package tlc2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import tlc2.Utils.Pair;
import tlc2.tool.EKState;
import tlc2.tool.ExtKripke;
import tlc2.tool.StateVarBasicType;
import tlc2.tool.StateVarFunctionType;
import tlc2.tool.StateVarType;
import tlc2.tool.StateVariable;


public class RobustDiffRep {
	private static final String DIFF_REP_FILE = "diff_rep_file";
	private static final String DIFF_REP_FILE1 = "diff_rep_file1";
	private static final String DIFF_REP_FILE2 = "diff_rep_file2";
	
	private static final String CONST_VALUE_CONSTRAINT = "const_value_constraint";
	private static final String CONST_VALUE_CONSTRAINT1 = "const_value_constraint1";
	private static final String CONST_VALUE_CONSTRAINT2 = "const_value_constraint2";
	
	private static final String SEPARATOR_FILE = "separator_file";
	private static final String SEPARATOR1_FILE = "separator1_file";
	private static final String SEPARATOR2_FILE = "separator2_file";
	
	private static final String DIFF_REP_STATES_EMPTY = "diff_rep_states_empty";
	private static final String DIFF_REP_STATES1_EMPTY = "diff_rep_states1_empty";
	private static final String DIFF_REP_STATES2_EMPTY = "diff_rep_states2_empty";
	
	private static final String GROUP_NAMES = "group_names";
	private static final String GROUP_NAMES1 = "group_names1";
	private static final String GROUP_NAMES2 = "group_names2";

	private static final String SORTS_MAP_FILE = "sorts_map_file";
	private static final String SORTS_MAP1_FILE = "sorts_map_file1";
	private static final String SORTS_MAP2_FILE = "sorts_map_file2";

	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	private static final String NEW_LINE = "\n";
	private static final String UNDERSCORE = "_";
	private static final String DIFF_REP = "diff_rep";
	private static final String DOT_TXT = ".txt";
	
	public enum SpecScope {
		Spec, Spec1, Spec2
	}
	
	public static String keyForSpecScope(SpecScope scope, String key, String key1, String key2) {
		switch (scope) {
		case Spec:
			return key;
		case Spec1:
			return key1;
		case Spec2:
			return key2;
		}
		throw new RuntimeException("Invalid SpecScope provided");
	}
	
	
	private final String specName;
	private final SpecScope specScope;
	private final String outputLocation;
	private final Set<EKState> safetyBoundary;
	private final Map<String, Set<EKState>> boundariesByGroup;
	private Map<String, String> jsonStrs;
	private Map<String, List<String>> jsonLists;
	
	public RobustDiffRep(String specName, SpecScope scope, String outputLoc, Set<EKState> safetyBoundary, Map<String, Set<EKState>> boundariesByGroup,
			Map<String,String> jsonStrs, Map<String, List<String>> jsonLists) {
		this.specName = specName;
		this.specScope = scope;
		this.safetyBoundary = safetyBoundary;
		this.boundariesByGroup = boundariesByGroup;
		this.outputLocation = outputLoc;
		this.jsonStrs = jsonStrs;
		this.jsonLists = jsonLists;
		
    	final String groupNamesKey = RobustDiffRep.keyForSpecScope(specScope, GROUP_NAMES, GROUP_NAMES1, GROUP_NAMES2);
    	this.jsonLists.put(groupNamesKey, new ArrayList<>(this.boundariesByGroup.keySet()));

    	final String diffRepEmptyKey = RobustDiffRep.keyForSpecScope(specScope, DIFF_REP_STATES_EMPTY, DIFF_REP_STATES1_EMPTY, DIFF_REP_STATES2_EMPTY);
    	this.jsonStrs.put(diffRepEmptyKey, this.safetyBoundary.size() > 0 ? FALSE : TRUE);
	}
	
	public void writeBoundary() {
		final String fileKeyBase = keyForSpecScope(specScope, DIFF_REP_FILE, DIFF_REP_FILE1, DIFF_REP_FILE2);
		for (final String groupName : this.boundariesByGroup.keySet()) {
			final Set<EKState> group = this.boundariesByGroup.get(groupName);
			final String fileName = this.specName + UNDERSCORE + groupName + UNDERSCORE + DIFF_REP + DOT_TXT;
			final String filePath = this.outputLocation + fileName;
			final String diffRepFileNameKey = fileKeyBase + UNDERSCORE + groupName;
	    	final String output = String.join(NEW_LINE, Utils.toStringArray(group));
	    	Utils.writeFile(filePath, output);
	    	this.jsonStrs.put(diffRepFileNameKey, filePath);
		}
	}
	
	public void writeBoundaryFOLSeparatorFile(final TLC tlcTypeOK) {
		for (final String groupName : this.boundariesByGroup.keySet()) {
			final Set<EKState> group = this.boundariesByGroup.get(groupName);
			createDiffStateRepFormula(group, tlcTypeOK, groupName);
		}
	}
	
	private void createDiffStateRepFormula(final Set<EKState> posExamples, final TLC tlcTypeOK, final String groupName) {
		/*
    	final ExtKripke stateSpaceKripke = tlcTypeOK.getKripke();
    	final Set<EKState> stateSpace = stateSpaceKripke.reach();
    	
    	// we pull the domain of every var from the entire state space
    	final Set<StateVariable> allStateVars = StateVariable.getStateVariables(stateSpace);
    	
    	// we decide which values are "const" from the posExamples. the idea here is that if
    	// a state variable has the same value in every positive example, then the constraint
    	// for the state variable is obvious: it's just the "const" value.
    	// in practice this is very nie because it reduces the burden of the FOL sep tool
    	// (since the tool doesn't tend to work well for large/complicated tasks).
    	final Set<Pair<String, String>> posExampleVarValues = posExamples
    			.stream()
    			.map(ex -> Utils.extractKeyValuePairsFromState(ex))
    			.flatMap(List::stream)
    			.collect(Collectors.toSet());
    	
    	// we also look at the domain of each variable restricted to the posExamples, but this
    	// is ONLY for figuring out whether each variable has a const value or not.
    	Map<String,Set<String>> posExampleVarDomains = new HashMap<>();
    	for (final Pair<String, String> kv : posExampleVarValues) {
    		final String var = kv.first;
    		final String val = kv.second;
    		if (!posExampleVarDomains.containsKey(var)) {
    			posExampleVarDomains.put(var, new HashSet<>());
    		}
    		posExampleVarDomains.get(var).add(val);
    	}
    	
    	// the set of state vars with non-const values, i.e. the domain has more than one element
    	// when we look through the posExamples.
    	final Set<String> nonConstValueVarStrs = posExampleVarDomains
    			.entrySet()
    			.stream()
    			.filter(e -> e.getValue().size() > 1)
    			.map(e -> e.getKey())
    			.collect(Collectors.toSet());
    	// same as nonConstValueVarStrs, but we collect the StateVariable objects
    	final Set<StateVariable> nonConstValueVars = allStateVars
    			.stream()
    			.filter(v -> nonConstValueVarStrs.contains(v.getName()))
    			.collect(Collectors.toSet());
    	// even though the "const value" vars have one value in the posExamples, the state var
    	// may have a domain larger than one element. therefore we need to track which "const value"
    	// we want when writing out the const-value var info.
    	final Map<String, String> constValueValues = posExampleVarDomains
    			.entrySet()
    			.stream()
    			.filter(e -> e.getValue().size() == 1)
    			.collect(Collectors.toMap(e -> e.getKey(), e -> Utils.singletonGetElement(e.getValue())));

    	// diffRepStateStrs is the set of positive examples
    	// notDiffStateStrs is the set of negative examples
    	final Set<EKState> negExamples = Utils.setMinus(stateSpace, posExamples);

    	if (!constValueValues.isEmpty()) {
    		final String constValueConstraintKeyBase = RobustDiffRep.keyForSpecScope(specScope, CONST_VALUE_CONSTRAINT, CONST_VALUE_CONSTRAINT1, CONST_VALUE_CONSTRAINT2);
    		final String constValueConstraintKey = constValueConstraintKeyBase + UNDERSCORE + groupName;
    		final String constValueConstraint = buildConstValueConstraint(constValueValues, this.jsonStrs);
            this.jsonStrs.put(constValueConstraintKey, constValueConstraint);
    	}
    	if (nonConstValueVars.size() > 0) {
    		final String separatorFileKeyBase = RobustDiffRep.keyForSpecScope(specScope, SEPARATOR_FILE, SEPARATOR1_FILE, SEPARATOR2_FILE);
    		final String sortsMapFileKeyBase = RobustDiffRep.keyForSpecScope(specScope, SORTS_MAP_FILE, SORTS_MAP1_FILE, SORTS_MAP2_FILE);
    		final String separatorFileKey = separatorFileKeyBase + UNDERSCORE + groupName;
    		final String sortsMapFileKey = sortsMapFileKeyBase + UNDERSCORE + groupName;
        	final String separatorFile = buildAndWriteSeparatorFOL(posExamples, negExamples, nonConstValueVars, this.specName, groupName, this.outputLocation);
        	if (separatorFile == null) {
        		// this is a really inelegant way to not write the FOL sep file if there aren't any negative examples
        		return;
        	}
        	final String sortsMapFile = writeSortsMap(nonConstValueVars, this.specName, groupName, this.outputLocation);
        	this.jsonStrs.put(separatorFileKey, separatorFile);
        	this.jsonStrs.put(sortsMapFileKey, sortsMapFile);
    	}
    	*/
    }
	
	
	/* Static helper methods */

    private static String buildConstValueConstraint(final Map<String, String> constValueValues, Map<String,String> jsonOutput) {
        Set<String> constraints = new HashSet<>();
        for (final String var : constValueValues.keySet()) {
        	final String val = constValueValues.get(var);
        	final String constr = var + " = " + val;
        	constraints.add(constr);
        }
        final String constValueConstraint = String.join(", ", constraints);
        return Utils.stringEscape(constValueConstraint);
    }
    
    private static String writeSortsMap(final Set<StateVariable> nonConstValueVars, final String specName, final String groupName, final String outputLoc) {
    	List<String> mappings = new ArrayList<>();
    	for (StateVariable var : nonConstValueVars) {
    		final StateVarType type = var.getType();
    		if (type instanceof StateVarFunctionType) {
    			// only write the domain + range sorts for a function. no need to include the TLA+ function type
    			final StateVarFunctionType ftype = (StateVarFunctionType) type;
        		final String domainSortMapping = "\"" + ftype.getDomain().getName() + "\":\"" + Utils.stringEscape(ftype.getDomain().toTlaType()) + "\"";
        		final String rangeSortMapping = "\"" + ftype.getRange().getName() + "\":\"" + Utils.stringEscape(ftype.getRange().toTlaType()) + "\"";
        		mappings.add(domainSortMapping);
        		mappings.add(rangeSortMapping);
    		}
    		else {
        		final String name = "\"" + type.getName() + "\"";
        		final String domain = type.toTlaType();
        		final String mapping = name + ":\"" + Utils.stringEscape(domain) + "\"";
        		mappings.add(mapping);
    		}
    	}
    	final String map = "{" + String.join(",", mappings) + "}";
    	
    	final String sortsMapFile = specName + UNDERSCORE + groupName + "_sorts_map.json";
    	final String path = outputLoc + sortsMapFile;
    	Utils.writeFile(path, map);
        return path;
    }
    
    private static String buildAndWriteSeparatorFOL(final Set<EKState> posExamples, final Set<EKState> negExamples, final Set<StateVariable> nonConstValueVars,
    		final String specName, final String groupName, final String outputLoc) {

    	// create FOL separator file
    	StringBuilder builder = new StringBuilder();

    	// collect types (sorts)
    	Set<String> sorts = new HashSet<>();
    	for (final StateVariable var : nonConstValueVars) {
    		final StateVarType type = var.getType();
    		if (type instanceof StateVarFunctionType) {
    			final StateVarFunctionType ftype = (StateVarFunctionType) type;
        		sorts.add("(sort " + ftype.getDomain().getName() + ")");
        		sorts.add("(sort " + ftype.getRange().getName() + ")");
    		}
    		else {
        		sorts.add("(sort " + type.getName() + ")");
    		}
    	}
    	
    	// collect state vars (relations and functions)
    	Set<String> relations = new HashSet<>();
    	Set<String> functions = new HashSet<>();
    	for (final StateVariable var : nonConstValueVars) {
    		final StateVarType type = var.getType();
    		if (type instanceof StateVarFunctionType) {
    			final StateVarFunctionType ftype = (StateVarFunctionType) type;
    			final String function = "(function " + var.getName() + " " + ftype.getDomain().getName() + " " + ftype.getRange().getName() + ")";
    			functions.add(function);
    		}
    		else {
    			final String relation = "(relation " + var.getName() + " " + type.getName() + ")";
    			relations.add(relation);
    		}
    	}

    	// collect constants (basic domain elements)
    	Set<StateVarBasicType> basicConsts = new HashSet<>();
    	for (final StateVariable var : nonConstValueVars) {
    		final StateVarType type = var.getType();
    		if (type instanceof StateVarFunctionType) {
    			final StateVarFunctionType ftype = (StateVarFunctionType) type;
        		Utils.assertTrue(ftype.getDomain() instanceof StateVarBasicType, "Expected domain to be a basic var type!");
        		Utils.assertTrue(ftype.getRange() instanceof StateVarBasicType, "Expected range to be a basic var type!");
    			basicConsts.add((StateVarBasicType) ftype.getDomain());
    			basicConsts.add((StateVarBasicType) ftype.getRange());
    		}
    		else {
        		Utils.assertTrue(type instanceof StateVarBasicType, "Expected basic var type!");
    			basicConsts.add((StateVarBasicType) type);
    		}
    	}
    	
    	// create const / element defs
    	Set<String> consts = new HashSet<>();
    	Set<String> modelElements = new HashSet<>();
    	Set<String> modelElementDefs = new HashSet<>();
    	for (final StateVarBasicType bconst : basicConsts) {
    		final String typeName = bconst.getName();
    		for (final String e : bconst.getDomain()) {
    			//final String elem = valueToConstantMap.get(e);
    			final String elem = "Ee_eE" + toSeparatorString(e) + "_" + typeName;
    			final String elemConst = elem + "Const";
    	    	consts.add("(constant " + elem + " " + typeName + ")");
    	    	modelElements.add("(" + elemConst + " " + typeName + ")");
    	    	modelElementDefs.add("(= " + elem + " " + elemConst + ")");
    		}
    	}
    	
    	
    	// print everything
    	builder.append(String.join("\n", sorts));
    	builder.append("\n\n");
    	builder.append(String.join("\n", relations));
    	builder.append("\n\n");
    	builder.append(String.join("\n", functions));
    	builder.append("\n\n");
    	builder.append(String.join("\n", consts));
    	builder.append("\n\n");
    	
    	// models
    	final Set<String> nonConstValueVarsAsStrings = nonConstValueVars
    			.stream()
    			.map(v -> v.getName())
    			.collect(Collectors.toSet());
    	final Map<String, StateVariable> varNamesMap = nonConstValueVars
    			.stream()
    		   .collect(Collectors.toMap(StateVariable::getName, Function.identity()));
    	boolean atLeastOneNegExample = false;
    	Set<String> posModels = new HashSet<>();
    	for (EKState s : posExamples) {
    		final String pos = toSeparatorModel(s, "+", modelElements, modelElementDefs, nonConstValueVarsAsStrings, varNamesMap);
    		if (pos != null) {
	    		posModels.add(pos);
	    		builder.append(pos);
    		}
    	}
		final int maxLen = 999999999;
		final int maxNegExamples = Utils.maxNegExamples();
		int numNegExamplesIncluded = 0;
		int numNegExamplesSkipped = 0;
    	for (EKState s : negExamples) {
    		final String neg = toSeparatorModel(s, "-", modelElements, modelElementDefs, nonConstValueVarsAsStrings, varNamesMap);
    		if (neg != null && !posModels.contains(neg.replace('-', '+'))) {
    			atLeastOneNegExample = true;
    			if (builder.length() < maxLen && numNegExamplesIncluded < maxNegExamples) {
    				++numNegExamplesIncluded;
    				builder.append(neg);
    			} else {
    				++numNegExamplesSkipped;
    			}
    		}
    	}
    	if (numNegExamplesSkipped > 0) {
    		System.err.println("WARNING: the state space is very large. Including " + numNegExamplesIncluded +
    				" negative examples and skipping " + numNegExamplesSkipped +
    				" negative examples during formula inference for group " + groupName + ".");
    	}

		// this is a really inelegant way to not write the FOL sep file if there aren't any negative examples
    	if (!atLeastOneNegExample) {
    		return null;
    	}
    	
    	final String separatorFile = specName + UNDERSCORE + groupName + ".fol";
    	final String path = outputLoc + separatorFile;
    	Utils.writeFile(path, builder.toString());
        return path;
    }
    
    private static String toSeparatorModel(final EKState tlaState, final String label, final Set<String> modelElements,
    		final Set<String> modelElementDefs, final Set<String> nonConstValueVars, final Map<String, StateVariable> varNamesMap) {
    	final String sms = toSeparatorModelString(tlaState, nonConstValueVars, varNamesMap);
    	if (sms == null) {
    		return null;
    	}
    	final String elementsStr = String.join(" ", modelElements);
    	
        StringBuilder builder = new StringBuilder();
    	builder.append("(model ").append(label).append("\n");
    	builder.append("    (");
    	builder.append(elementsStr);
    	builder.append(")\n");
    	for (String elemDef : modelElementDefs) {
        	builder.append("    " + elemDef + "\n");
    	}
    	builder.append(sms);
    	builder.append("\n)\n");
        return builder.toString();
    }
    
    private static String toSeparatorModelString(final EKState tlaState, final Set<String> nonConstValueVars, final Map<String, StateVariable> varNamesMap) {
    	ArrayList<String> separatorConjuncts = new ArrayList<>();
    	Utils.assertTrue(false, "Methods is unsupported!");
    	ArrayList<Pair<String,String>> stateAssignments = null; // Utils.extractKeyValuePairsFromState(tlaState);
    	for (Pair<String,String> assg : stateAssignments) {
    		final String var = assg.first;
    		final String val = assg.second;
    		if (nonConstValueVars.contains(var)) {
    			final boolean functionValue = val.contains("|->");
    			if (functionValue) {
    				// yea sorry my code is awful
    				final String f = var;
    				final StateVariable sv = varNamesMap.get(f);
    				final StateVarType type = sv.getType();
    				Utils.assertTrue(type instanceof StateVarFunctionType, "Expected function type!");
    				final StateVarFunctionType ftype = (StateVarFunctionType) type;
    				final String xSort = ftype.getDomain().getName();
    				final String ySort = ftype.getRange().getName();
    				
    				final String[] parts = val.split(Pattern.quote(","));
    				for (final String asg : parts) {
    					final String[] kv = asg.split(Pattern.quote("|->"));
    					Utils.assertTrue(kv.length == 2, "Found malformed function mapping!");
    					final String domainVal = kv[0].replaceAll("[\\[\\]]", "").trim();
    					final String rangeVal = kv[1].replaceAll("[\\[\\]]", "").trim();
    	        		final String x = "Ee_eE" + toSeparatorString(domainVal) + "_" + xSort + "Const";
    	        		final String y = "Ee_eE" + toSeparatorString(rangeVal) + "_" + ySort + "Const";
    	        		final String sepConjunct = "    (= (" + f + " " + x + ") " + y + ")";
	        			separatorConjuncts.add(sepConjunct);
    	        		if (!ftype.getDomain().getRawTlcDomain().contains(domainVal) || !ftype.getRange().getRawTlcDomain().contains(rangeVal)) {
    	        			// if we see an element in the domain or range of the function that isn't part of the values we care about,
    	        			// then don't include this sample
    	        			return null;
    	        		}
    				}
    			}
    			else {
    				final StateVariable sv = varNamesMap.get(var);
    				final String sort = sv.getType().getName();
	        		final String sepFolVal = "Ee_eE" + toSeparatorString(val) + "_" + sort + "Const";
	        		final String sepConjunct = "    (" + var + " " + sepFolVal + ")";
	        		separatorConjuncts.add(sepConjunct);
	        		if (!sv.getType().getRawTlcDomain().contains(val)) {
	        			// if we see an element in the domain that isn't part of the values we care about, then don't include this sample
	        			return null;
	        		}
    			}
    		}
    	}
		return String.join("\n", separatorConjuncts);
    }
    
    private static String toSeparatorString(String str) {
    	return str
    			.replaceAll("[\\s]", "Ss_sS")
    			.replaceAll("[\"]", "Qq_qQ")
    			.replaceAll("[{]", "Lp_pL")
    			.replaceAll("[}]", "Rp_pR")
    			.replaceAll("[,]", "Cc_cC");
    }
}
