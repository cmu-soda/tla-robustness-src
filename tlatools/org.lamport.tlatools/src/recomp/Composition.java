package recomp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tlc2.TLC;
import tlc2.Utils;
import tlc2.tool.impl.FastTool;

public class Composition {
	
	public static List<String> symbolicCompose(final String tla, final String cfg,
			final String recompType, final String recompFile, final List<String> rawComponents) {
		// interfaceOrdering() trims unneeded components. Don't use the ordering, but do use it to trim components.
		final Set<String> neededComponents = interfaceOrdering(rawComponents)
				.stream()
				.collect(Collectors.toSet());
		final List<String> trimmedComponents = rawComponents
				.stream()
				.filter(c -> neededComponents.contains(c))
				.collect(Collectors.toList());
		
		final boolean useHeuristic = !recompType.equals("CUSTOM") && !recompType.equals("NAIVE");
		final List<String> orderedComponents = useHeuristic ? dataFlowOrdering(tla, cfg, trimmedComponents) : trimmedComponents;
		
		List<List<String>> groupings = new ArrayList<>();
		
		// custom re-mapping
		if (recompType.equals("CUSTOM")) {
			Utils.fileContents(recompFile)
				.stream()
				.map(l -> Utils.toArrayList(l.split(",")))
				.map(a -> a.stream().map(c -> c.trim()).collect(Collectors.toList()))
				.forEach(a -> groupings.add(a));
			
			// sanity check
			final Set<String> rawCmptSet = orderedComponents.stream().collect(Collectors.toSet());
			final Set<String> grCmptSet = groupings
					.stream()
					.reduce((Set<String>) new HashSet<String>(),
							(acc, g) -> Utils.union(acc, g.stream().collect(Collectors.toSet())),
							(s, t) -> Utils.union(s, t));
			if (!grCmptSet.equals(rawCmptSet)) {
				// some extra debugging info for the user
				System.err.println("Components expected:");
				for (String s : rawCmptSet) {
					System.err.println("  " + s);
				}
				System.err.println("Components seen:");
				for (String s : grCmptSet) {
					System.err.println("  " + s);
				}
				Utils.assertTrue(false, "Invalid custom recomp map!");
			}
		}
		// naive re-mapping
		else if (recompType.equals("NAIVE")) {
			for (final String c : orderedComponents) {
				groupings.add(List.of(c));
			}
		}
		// by default we create the re-mapping using the heuristic
		else {
			List<String> curGroup = new LinkedList<>();
			groupings.add(curGroup);
			String prevComponent = orderedComponents.get(0);
			curGroup.add(prevComponent);
			for (int i = 1; i < orderedComponents.size(); ++i) {
				final String curComponent = orderedComponents.get(i);
				// if the vars of a component occur alone in at least one action then do not group it with the previous component. otherwise:
				// only group adjacent components together if their vars overlap in at least one action
				if (varsAppearAloneInAtLeastOneAction(tla, cfg, curComponent) ||
						!varsOverlapInAtLeastOneAction(tla, cfg, prevComponent, curComponent)) {
					curGroup = new LinkedList<>();
					groupings.add(curGroup);
				}
				curGroup.add(curComponent);
				prevComponent = curComponent;
			}
		}
		
		final boolean allCompoments = orderedComponents.size() == rawComponents.size();
		return Decomposition.decompForSymbolicCompose(tla, cfg, groupings, allCompoments);
	}
	
	/**
	 * Orders the components by how they talk to each other through their interfaces (alphabets).
	 * This method will trim components that can (provably) not affect verification.
	 * @param rawComponents
	 * @return
	 */
	private static List<String> interfaceOrdering(final List<String> rawComponents) {
		if (rawComponents.isEmpty()) {
			return rawComponents;
		}
		
    	final String noInvsCfg = "no_invs.cfg";
    	final List<Set<String>> alphabets = rawComponents
    			.stream()
    			.map(c -> TLC.actionsInSpec(c, noInvsCfg))
    			.collect(Collectors.toList());
    	
    	// gather all components that use the interface of the current component Ci
    	final Set<Integer> allIndices =
    			IntStream
    			.range(0, rawComponents.size())
    		    .boxed()
    		    .collect(Collectors.toSet());
    	Set<String> alphSoFar = new HashSet<>();
    	List<String> components = new ArrayList<>();
    	Set<Integer> indicesInPlace = new HashSet<>();
    	
    	// place the first component at the front
    	components.add(rawComponents.get(0));
    	indicesInPlace.add(0);
		alphSoFar.addAll(alphabets.get(0));
    	
    	// place all components
    	while (!indicesInPlace.containsAll(allIndices)) {
    		// find the components whose alphabet intersects with alphSoFar
    		final Set<Integer> interfaceIndices = Utils.setMinus(allIndices, indicesInPlace)
    				.stream()
    				.filter(i -> !Utils.intersection(alphabets.get(i), alphSoFar).isEmpty())
    				.collect(Collectors.toSet());
    		if (interfaceIndices.isEmpty()) {
    			// if no components intersect with the prior alphabet then it can't affect verification
    			break;
    		}
    		interfaceIndices
					.stream()
					.forEach(i -> {
						components.add(rawComponents.get(i));
						alphSoFar.addAll(alphabets.get(i));
					});
			indicesInPlace.addAll(interfaceIndices);
    	}
    	
    	return components;
	}
	
	/**
	 * Orders the components using a "data flow" heuristic, where the data starts from the variables that occur
	 * in the safety property and "flow" to variables that occur (as guards / primed) in the same action. This
	 * ordering essentially views each component as a set of state variables.
	 * @param tla The monolithic TLA+ file
	 * @param cfg The config for the monolithic TLA+ file
	 * @param rawComponents
	 * @return
	 */
	private static List<String> dataFlowOrdering(final String tla, final String cfg, final List<String> rawComponents) {
		if (rawComponents.isEmpty()) {
			return rawComponents;
		}
		
    	final String noInvsCfg = "no_invs.cfg";
    	final List<Set<String>> stateVars = rawComponents
    			.stream()
    			.map(c -> TLC.stateVarsInSpec(c, noInvsCfg))
    			.collect(Collectors.toList());
    	
    	// collect the state vars in the safety property
    	TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	final Set<String> invariantVars = tlc.stateVariablesUsedInInvariants();
    	final Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(invariantVars);
    	
    	// sanity check--the first component should contain the property vars
    	Utils.assertTrue(propertyVars.equals(stateVars.get(0)), "First component should contain all property vars!");
    	
    	
    	// STEP 1: assign a partial order to the state vars based the data flow of the vars
    	Set<Utils.Pair<String,String>> partialOrder = new HashSet<>();
    	
    	// all vars from the same component are equal to each other in the partial order
    	for (final Set<String> cmptVars : stateVars) {
    		for (final String v1 : cmptVars) {
        		for (final String v2 : cmptVars) {
            		partialOrder.add(new Utils.Pair<>(v1, v2));
        		}
    		}
    	}
    	
    	// add "data flow" relations to the partial order
    	Set<String> visitedVars = new HashSet<>();
    	List<Set<String>> queue = new LinkedList<>();
    	queue.add(propertyVars);
    	while (!queue.isEmpty()) {
    		final Set<String> currentVars = queue.remove(0);
        	visitedVars.addAll(currentVars);
    		
        	for (final String v : currentVars) {
        		// find all variables that occur in the same actions as v
        		final Set<String> flowToVars = tlc.stateVarsInSameAction(Set.of(v));
        		flowToVars.removeAll(visitedVars);
        		
        		// add flowToVars to partial order
        		for (final String ftv : flowToVars) {
        			partialOrder.add(new Utils.Pair<>(v, ftv));
        		}
        		
        		// prepare for next iteration
        		queue.add(flowToVars);
        	}
    	}
    	
    	// add transitive closure relations to the partial order
    	Utils.transitiveClosure(partialOrder);
    	
    	
    	// STEP 2: break ties (assign a total order to the state vars) based on which vars occur more (syntactically)
    	// in the monolithic spec
    	final Set<String> allStateVars = tlc.stateVarsInSpec();

		// find incomparable elements and assign a total order
		for (final String v1 : allStateVars) {
			for (final String v2 : allStateVars) {
				if (!v1.equals(v2)) {
					final Utils.Pair<String,String> order1 = new Utils.Pair<>(v1,v2);
					final Utils.Pair<String,String> order2 = new Utils.Pair<>(v2,v1);
					if (!partialOrder.contains(order1) && !partialOrder.contains(order2)) {
						// found incomparable elements
						// current tie breaker strategy: choose the variable that occurs more (syntactically) to be "larger"
						final int numOccurrencesV1 = tlc.numOccurrencesOutsideOfUNCHANGED(v1);
						final int numOccurrencesV2 = tlc.numOccurrencesOutsideOfUNCHANGED(v2);
						final Utils.Pair<String,String> tieBreaker = (numOccurrencesV1 < numOccurrencesV2) ? order1 : order2;
						partialOrder.add(tieBreaker);
				    	Utils.transitiveClosure(partialOrder);
					}
				}
			}
		}
    	
    	
    	// STEP 3: the total ordering on their state variables induces a total ordering over the components
    	
    	// build a map from state var -> component
    	Map<String,String> varToComponentMap = new HashMap<>();
    	for (int i = 0; i < stateVars.size(); ++i) {
    		final String component = rawComponents.get(i);
    		for (final String var : stateVars.get(i)) {
    			varToComponentMap.put(var, component);
    		}
    	}
    	
    	// replace state vars in the PO with the component they belong to. this will give us a total ordering over the
    	// components.
    	Set<Utils.Pair<String,String>> componentOrder = partialOrder
    			.stream()
    			.map(e -> new Utils.Pair<String,String>(varToComponentMap.get(e.first), varToComponentMap.get(e.second)))
    			.collect(Collectors.toSet());
    	/*for (final Utils.Pair<String,String> e : componentOrder) {
    		System.err.println("(" + e.first + ", " + e.second + ")");
    	}
    	System.err.println();*/
    	
    	// remove the largest element from <componentOrder> until it is empty
    	List<String> components = new ArrayList<>();
    	while (!componentOrder.isEmpty()) {
    		final String largestElem = Utils.largestElement(componentOrder);
    		components.add(largestElem);
    		componentOrder = componentOrder
    				.stream()
    				.filter(e -> !largestElem.equals(e.first) && !largestElem.equals(e.second))
    				.collect(Collectors.toSet());
    	}
    	
		return components;
	}

	/**
	 * Returns whether the state vars in the given <component> occur alone (without any other vars) in at
	 * least one action in the monolithic spec.
	 * @param tla
	 * @param cfg
	 * @param component
	 * @return
	 */
	private static boolean varsAppearAloneInAtLeastOneAction(final String tla, final String cfg, final String component) {
		TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	
    	final String noInvsCfg = "no_invs.cfg";
		TLC componentTlc = new TLC();
		componentTlc.initialize(component, noInvsCfg);
    	final Set<String> componentVars = componentTlc.stateVarsInSpec();
    	
    	// look through each action. if there exists an action with only state vars that are a subset of
    	// <componentVars> then we return true. otherwise, false.
    	final Map<String,Set<String>> varsPerAction = tlc.stateVarsPerAction();
    	for (final String act : tlc.actionsInSpec()) {
    		final Set<String> actVars = varsPerAction.get(act);
    		//!tlc.actionIsGuarded(act) && 
    		if (componentVars.containsAll(actVars)) {
    			return true;
    		}
    	}
    	return false;
	}
	
	/**
	 * Given two specifications <c1> and <c2>, this method will compute whether there is an action in the monolithic
	 * spec that refers to the variables of both <c1> and <c2>. In particular, this method will check if the variables
	 * that occur together are both primed or both unprimed.
	 * @param tla the monolithic spec
	 * @param cfg
	 * @param c1
	 * @param c2
	 * @return
	 */
	private static boolean varsOverlapInAtLeastOneAction(final String tla, final String cfg, final String c1, final String c2) {
		TLC tlc = new TLC();
    	tlc.initialize(tla, cfg);
    	
    	final String noInvsCfg = "no_invs.cfg";
		TLC c1Tlc = new TLC();
    	c1Tlc.initialize(c1, noInvsCfg);
		TLC c2Tlc = new TLC();
    	c2Tlc.initialize(c2, noInvsCfg);
    	
    	final Set<String> c1StateVars = c1Tlc.stateVarsInSpec();
    	final Set<String> c2StateVars = c2Tlc.stateVarsInSpec();
    	
    	// start of primed/unprimed specific code
    	final Set<String> primedStateVarsWithC1 = tlc.oneModeOfStateVarsInSameAction(c1StateVars, true);
    	final Set<String> unprimedStateVarsWithC1 = tlc.oneModeOfStateVarsInSameAction(c1StateVars, false);
    	
    	return !Utils.intersection(primedStateVarsWithC1, c2StateVars).isEmpty() &&
    			!Utils.intersection(unprimedStateVarsWithC1, c2StateVars).isEmpty();
    	//return !Utils.intersection(tlc.stateVarsInSameAction(c1StateVars), c2StateVars).isEmpty();
	}
	
    /**
     * Calculates the vars from bSpec that /may/ be needed to uphold the guarantees of the interface
     * provided in aSpec. We perform this calculation by consider all variables in bSpec that are not
     * exclusively in UNCHANGED blocks in the mutual actions of aSpec and bSpec.
     * If the parameter "minVars" is true, this method will choose the minimum vars needed to perform
     * the next slice.
     * @param aSpec
     * @param bSpec
     * @return
     */
    private static Set<String> calcPropertyVars(final String aSpec, final String aCfg, final String bSpec, final String bCfg, boolean minVars) {
    	final Set<String> aActions = TLC.actionsInSpec(aSpec, aCfg);
    	final Set<String> bActions = TLC.actionsInSpec(bSpec, bCfg);
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
    	final Set<String> bVars = TLC.stateVarsInSpec(bSpec, bCfg);
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
    	final Set<String> rawPropertyVars = minVars && !varsThatMayChange.isEmpty() ?
    			Utils.setOf( Utils.chooseOne(varsThatMayChange) ) :
    			varsThatMayChange;
    	
    	// also compute all vars that occur in the same expressions as rawPropertyVars
    	final Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(rawPropertyVars);
    	return propertyVars;
    }

    /**
     * Calculates the vars from bSpec that occur as a guard in at least one action in the interface between aSpec and bSpec,
     * i.e. intersection of their alphabets.
     * @param aSpec
     * @param bSpec
     * @return
     */
    private static Set<String> calcPropertyVarsByGuards(final String aSpec, final String aCfg, final String bSpec, final String bCfg) {
    	final Set<String> aActions = TLC.actionsInSpec(aSpec, aCfg);
    	final Set<String> bActions = TLC.actionsInSpec(bSpec, bCfg);
    	final Set<String> ifaceActions = Utils.intersection(aActions, bActions);
    	
    	TLC tlc = new TLC("b_" + bSpec);
    	tlc.initialize(bSpec, bCfg);
    	final FastTool ft = (FastTool) tlc.tool;
    	
    	// get the top level module and all op def nodes
    	final String moduleName = tlc.getModelName();
    	final ModuleNode mn = ft.getModule(moduleName);
    	final List<OpDefNode> moduleNodes = Utils.toArrayList(mn.getOpDefs())
    			.stream()
    			.filter(m -> !m.isStandardModule())
    			.filter(m -> ifaceActions.contains(m.getName().toString()))
    			.collect(Collectors.toList());
    	
    	// find vars that are occur as a guard in at least one action in ifaceActions in bSpec
    	final Set<String> bVars = TLC.stateVarsInSpec(bSpec, bCfg);
    	final Set<String> bVarsInGuards = bVars
    			.stream()
    			.filter(v -> {
    				return moduleNodes
    						.stream()
    						.anyMatch(n -> n.varOccursInGuard(v));
    			})
    			.collect(Collectors.toSet());
    	
    	// also compute all vars that occur in the same expressions as varsThatMayChange
    	final Set<String> propertyVars = tlc.stateVarsUsedInSameExprs(bVarsInGuards);
    	
    	return propertyVars;
    }
}
