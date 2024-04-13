package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import tlc2.Utils;
import tlc2.Utils.Pair;

public class StateVariable {
	private final String name;
	private final StateVarType type;
	
	private StateVariable(final String name, final StateVarType type) {
		this.name = name;
		this.type = type;
	}
	
	public String getName() {
		return this.name;
	}
	
	public StateVarType getType() {
		return this.type;
	}
	
	public String asDisjunctionOfAssignments() {
		final List<String> assignments = this.type.getRawTlcDomain()
			.stream()
			.map(s -> (this.name + " = " + s))
			.collect(Collectors.toList());
		return String.join(" \\/ ", assignments);
	}
	
	@Override
	public boolean equals(Object o) {
		if (o instanceof StateVariable) {
			StateVariable other = (StateVariable) o;
			return this.name.equals(other.name);
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		return this.name.hashCode();
	}
	
	
	/*
	public static Set<StateVariable> getStateVariables(final Set<EKState> stateSpace) {
    	// determine the domain for each state var
    	Map<String, Set<String>> varDomain = new HashMap<>();
    	for (final EKState state : stateSpace) {
    		ArrayList<Pair<String,String>> stateAssignments = Utils.extractKeyValuePairsFromState(state);
    		for (Pair<String,String> assg : stateAssignments) {
    			final String var = assg.first;
    			final String val = assg.second;
    			if (!varDomain.containsKey(var)) {
    				varDomain.put(var, new HashSet<>());
    			}
    			varDomain.get(var).add(val);
    		}
    	}
    	
    	// group variables by common domain
    	// variablesPerType : (domain) -> (variables whose type is /domain/)
    	Map<Set<String>, Set<String>> variablesPerType = new HashMap<>();
    	for (final String var : varDomain.keySet()) {
    		final Set<String> domain = varDomain.get(var);
    		if (!variablesPerType.containsKey(domain)) {
    			variablesPerType.put(domain, new HashSet<>());
    		}
    		variablesPerType.get(domain).add(var);
    	}

    	// for each group of variable in a common domain, assign a type. we store the
    	// results in a map of (var) -> (type) for convenience in the next step
    	int sortNum = 1;
    	Map<String, StateVarType> typePerVariable = new HashMap<>();
    	Map<Set<String>, StateVarType> domainToStateVar = new HashMap<>();
    	for (final Set<String> domain : variablesPerType.keySet()) {
    		final String typeName = "Sort" + sortNum++;
    		final StateVarType varType = StateVarType.createStateVarType(typeName, domain);
    		final Set<String> vars = variablesPerType.get(domain);
    		for (final String var : vars) {
    			typePerVariable.put(var, varType);
    		}
    		domainToStateVar.put(domain, varType);
    	}
    	
    	// create a StateVariable object for each var
    	Set<StateVariable> stateVars = new HashSet<>();
    	for (final String var : typePerVariable.keySet()) {
    		final StateVarType type = typePerVariable.get(var);
    		stateVars.add(new StateVariable(var, type));
    	}
    	
    	// set the domain and range for each function as a StateVarType
    	Set<StateVarFunctionType> functionTypes = stateVars.stream()
			.map(v -> v.getType())
			.filter(t -> (t instanceof StateVarFunctionType))
			.map(t -> ((StateVarFunctionType)t))
			.collect(Collectors.toSet());
    	
    	for (StateVarFunctionType ft : functionTypes) {
    		do {
				// try to look up the domain in the existing types
				final Set<String> rawDomain = ft.getRawDomain();
				if (domainToStateVar.containsKey(rawDomain)) {
					final StateVarType domainType = domainToStateVar.get(rawDomain);
					ft.setDomain(domainType);
				}
				else {
					// if the domain doesn't already exist then we need to create a new type.
					// we also add it to the domainToStateVar map so the range can potentially
					// make use of it.
		    		final String typeName = "Sort" + sortNum++;
					final StateVarType domainType = StateVarType.createStateVarType(typeName, rawDomain);
					ft.setDomain(domainType);
					domainToStateVar.put(rawDomain, domainType);
				}
    		} while(false);
    		do {
				// try to look up the range in the existing types
				final Set<String> rawRange = ft.getRawRange();
				if (domainToStateVar.containsKey(rawRange)) {
					final StateVarType rangeType = domainToStateVar.get(rawRange);
					ft.setRange(rangeType);
				}
				else {
					// if the domain doesn't already exist then we need to create a new type.
					// we also add it to the domainToStateVar map so the range can potentially
					// make use of it.
		    		final String typeName = "Sort" + sortNum++;
					final StateVarType rangeType = StateVarType.createStateVarType(typeName, rawRange);
					ft.setRange(rangeType);
					domainToStateVar.put(rawRange, rangeType);
				}
    		} while(false);
    	}
    	
    	return stateVars;
	}*/
}
