// an Extended Kripke Structure
// "extended" just means we keep track of some extra info

package tlc2.tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import tlc2.TLC;
import tlc2.Utils;
import tlc2.Utils.Pair;
import tlc2.value.impl.Value;

import java.lang.StringBuilder;
import tlc2.tool.impl.FastTool;

import tla2sany.parser.SyntaxTreeNode;


public class ExtKripke {
	private static final String UNCHANGED = "UNCHANGED";
	private static final String INSTANCE = "INSTANCE";
	private static final String VARIABLES = "VARIABLES";
	private static final String WITH = "WITH";
	private static final String VARS = "Vars";
	private static final String NEXT = "Next";
	private static final String INIT = "Init";
	private static final String TYPE_OK = "TypeOK";
    
    private enum BoundaryType {
    	safety, error
    }
    
    private Set<EKState> initStates;
    private Set<EKState> allStates;
    private Set<EKState> badStates;
    private Set<Pair<EKState,EKState>> delta;
    private Map<Pair<EKState,EKState>, String> deltaActions;
    private Map<Pair<EKState,EKState>, Set<String>> deltaActionsWithParams;
    private Set<EKState> envStates;

    public ExtKripke() {
    	this.initStates = new HashSet<>();
        this.allStates = new HashSet<>();
        this.badStates = new HashSet<>();
        this.delta = new HashSet<>();
        this.deltaActions = new HashMap<>();
        this.deltaActionsWithParams = new HashMap<>();
    	this.envStates = new HashSet<>();
    }

    public ExtKripke(final ExtKripke src) {
    	this.initStates = new HashSet<>(src.initStates);
    	this.allStates = new HashSet<>(src.allStates);
    	this.badStates = new HashSet<>(src.badStates);
    	this.delta = new HashSet<>(src.delta);
    	this.deltaActions = new HashMap<>(src.deltaActions);
    	this.deltaActionsWithParams = new HashMap<>(src.deltaActionsWithParams);
    	this.envStates = new HashSet<>(src.envStates);
    }

	private static Set<String> getSpecActions(TLC tlc) {
		FastTool ft = (FastTool) tlc.tool;
		return Utils.toArrayList(ft.getActions())
				.stream()
				.map(a -> a.getName().toString())
				.collect(Collectors.toSet());
	}

	public static String composeSpecs(String[] args) {
		final String tla1 = args[1];
		final String cfg1 = args[2];
		final String tla2 = args[3];
		final String cfg2 = args[4];
		
		TLC tlc1 = new TLC("spec1");
		TLC.runTLC(tla1, cfg1, tlc1);

		TLC tlc2 = new TLC("spec2");
		TLC.runTLC(tla2, cfg2, tlc2);

		final Set<String> act1 = getSpecActions(tlc1);
		final Set<String> act2 = getSpecActions(tlc2);
		final Set<String> mutualActs = Utils.intersection(act1, act2);
		final Set<String> onlyAct1 = Utils.setMinus(act1, mutualActs);
		final Set<String> onlyAct2 = Utils.setMinus(act2, mutualActs);
		FastTool ft1 = (FastTool) tlc1.tool;
		FastTool ft2 = (FastTool) tlc2.tool;

		String fileName1 = tlc1.getMainFile();
		String fileName2 = tlc2.getMainFile();

		final String parameters = 
				(TLC.getTransitionRelationNode(ft1, tlc1, "Next").getBdedQuantSymbolLists() == null? 
						"false" : "true");

		ArrayList<String> vars1 = Utils.toArrayList(ft1.getVarNames());
		ArrayList<String> vars2 = Utils.toArrayList(ft2.getVarNames());

		String[] saveParams = null;
		String parameterNoParen = "";
		String parameterFormula = "";
		
		if (parameters.equals("true")) {
			saveParams = new String[TLC.getTransitionRelationNode(ft1, tlc1, "Next").getBdedQuantSymbolLists().length];
			for (int i = 0; i < TLC.getTransitionRelationNode(ft1, tlc1, "Next").getBdedQuantSymbolLists().length; i++) {
				for (int j = 0; j < TLC.getTransitionRelationNode(ft1, tlc1, "Next").
						getBdedQuantSymbolLists()[i].length; j++) {
					saveParams[i] = TLC.getTransitionRelationNode(ft1, tlc1, "Next").
							getBdedQuantSymbolLists()[i][j].getName().toString();
				}
			}
		} 
		
		String parameter = (!(parameters.equals("true"))? "" : "(" + String.join(",", saveParams) + ")");

		if (parameters.equals("true")) {
			parameterNoParen = TLC.getTransitionRelationNode(ft1, tlc1, "Next").
					getBdedQuantSymbolLists()[0][0].getName().toString();
			parameterFormula = ((SyntaxTreeNode)TLC.getTransitionRelationNode(ft1, tlc1, "Next").
					getBdedQuantBounds()[0].stn).heirs()[1].getImage().toString();
		}

		ArrayList<String> nextNames = new ArrayList<String>();

		String saveVars = String.join(", " , vars1) + ", " + String.join(", " , vars2);

		String full = "\n" + VARIABLES + " " + saveVars + "\n\nvars == <<"  + saveVars + ">> \n\n" 
				+ fileName1 + VARS + " == <<" + String.join(", ", vars1) + ">> \n" + fileName2 
				+ VARS + " == <<" + String.join(", ", vars2) + ">> \n\n" 
				+ formatInstance(fileName1, vars1) + formatInstance(fileName2, vars2) 
				+ (!(parameters.equals("true"))? "" : 
					"\n" + parameterFormula + " == " + fileName1 + "!" + parameterFormula)
				+ "\n\n" + INIT + " == " + fileName1 + "!" + INIT + " /\\ " + fileName2 
				+  "!" + INIT + " \n\n";

		for (String val : mutualActs) {
			full += val + parameter + " == " + fileName1 + "!" + val + parameter + " /\\ "
					+ fileName2 + "!" + val + parameter + "\n\n";
			nextNames.add(val);
		}

		full += formatNonSharedActions(onlyAct1, fileName1, fileName2, nextNames, parameter)
				+ formatNonSharedActions(onlyAct2, fileName2, fileName1, nextNames, parameter) 
				+ NEXT + (!(parameters.equals("true"))? " == \n    \\/" : " == \n \\E " + parameterNoParen 
						+ " \\in " + parameterFormula + ":\n    \\/") + String.join(parameter + " \n    \\/ ", nextNames) 
						+ parameter + "\n\nSpec == " + INIT + " /\\ " + "[]["+ NEXT + "]_vars\n\n" 
						+ TYPE_OK + " == " + fileName1 + "!" + TYPE_OK 
						+ " /\\ " + fileName2 + "!" + TYPE_OK + "\n";

		return full;
	}



	private static String formatInstance(String fileName, ArrayList<String> vars) {
		String save = "";
		save += fileName + 
				" == " + INSTANCE + " " + fileName + "\n\t\t" + WITH + " " + vars.get(0) 
				+ " <- " + vars.get(0) + (vars.size() != 1? ",\n" : "\n");

		for (int i = 1; i < vars.size(); i++) {
			if (i == vars.size() - 1) {
				save += "\t\t     " + vars.get(i) + " <- " + vars.get(i) + "\n";
			} else {
				save += "\t\t     " + vars.get(i) + " <- " + vars.get(i) + ",\n";
			}
		}

		return save;
	}



	private static String formatNonSharedActions(Set<String> actions, 
			String fileName1, String fileName2, ArrayList<String> nextNames, String parameters) {
		String save = "";
		for (String val : actions) {
			save += val + parameters + " == " + UNCHANGED + " " + fileName2 + VARS + " /\\ " 
					+ fileName1 + "!" + val + parameters + "\n\n";
			nextNames.add(val);
		}
		return save;
	}

	// assumes that the state space of srcClosed is more refined than the state space of srcM.
	// this assumption is generally valid because the closed system is composed of M, and hence
	// contains all state vars that are in M.
	public ExtKripke(final ExtKripke srcM, final ExtKripke srcClosed) {
		this(srcM);
		if (!srcClosed.badStates.isEmpty()) {
			throw new RuntimeException("Closed system is not safe!");
		}
		if (!srcM.envStates.isEmpty()) {
			throw new RuntimeException("M contains env states!");
		}

		// add env states. small optimization: we know that all env states are safe
		final Set<EKState> srcMGoodStates = Utils.setMinus(srcM.allStates, srcM.badStates);
		for (final EKState s : srcMGoodStates) {
			if (refinedContainerContainsAbstractState(srcClosed.allStates, s)) {
				this.envStates.add(s);
			}
		}
	}

	private static boolean refinedContainerContainsAbstractState(final Set<EKState> container, final EKState abstrState) {
		for (final EKState refinedState : container) {
			if (refinedImpliesAbstractState(refinedState, abstrState)) {
				return true;
			}
		}
		return false;
	}

	private static boolean refinedImpliesAbstractState(final EKState refinedState, final EKState abstrState) {
		final Set<Pair<String,String>> refinedKvPairs = new HashSet<>(Utils.extractKeyValuePairsFromState(refinedState));
		final Set<Pair<String,String>> abstrKvPairs = new HashSet<>(Utils.extractKeyValuePairsFromState(abstrState));
		return refinedKvPairs.containsAll(abstrKvPairs);
	}

	// pre-processing

	// bad initial states are explicitly added (via addBadState()) in ModelChecker.java
	public void addInitState(TLCState s) {
		final String sName = Utils.normalizeStateString(s.toString());
		final EKState eks = new EKState(sName);
		allStates.add(eks);
		initStates.add(eks);
	}

	public void addGoodState(TLCState s) {
		final String sName = Utils.normalizeStateString(s.toString());
		final EKState eks = new EKState(sName);
		allStates.add(eks);
	}

	public void addBadState(TLCState s) {
		final String sName = Utils.normalizeStateString(s.toString());
		final EKState eks = new EKState(sName);
		allStates.add(eks);
		badStates.add(eks);
	}

    public void addTransition(Action act, TLCState src, TLCState dst) {
    	final String srcName = Utils.normalizeStateString(src.toString());
    	final String dstName = Utils.normalizeStateString(dst.toString());
    	final EKState srcEks = new EKState(srcName);
    	final EKState dstEks = new EKState(dstName);
    	final Pair<EKState,EKState> transition = new Pair<>(srcEks, dstEks);
    	
    	final String actName = act.getName().toString();
    	Utils.assertNotNull(actName, "TLC added null action name to an ExtKripke instance!");
    	delta.add(transition);
    	deltaActions.put(transition, actName);

    	// add param values to the action
    	final List<String> paramKeys = Utils.actionParams(act);
    	final Map<String, Value> mp = act.con.toStrMap();
    	ArrayList<String> params = new ArrayList<>();
    	for (final String k : paramKeys) {
    		final Value val = mp.get(k);
    		final String sk = val.toString().replace("\"", "");
    		params.add(sk);
    	}
    	final String actNameWParams = actName + "_" + String.join("_", params);
    	if (!deltaActionsWithParams.containsKey(transition)) {
        	deltaActionsWithParams.put(transition, new HashSet<>());
    	}
    	deltaActionsWithParams.get(transition).add(actNameWParams);
    }


	// post-processing

	public boolean isEmpty() {
		return this.allStates.isEmpty() || this.initStates.isEmpty();
	}

	public boolean isSafe() {
		return this.badStates.isEmpty();
	}

	public Set<EKState> reach() {
		return this.allStates;
	}

	public boolean isBadState(final EKState s) {
		return this.badStates.contains(s);
	}

	public ExtKripke createErrPre() {
		Set<EKState> errStates = notAlwaysNotPhiStates();
		Set<Pair<EKState,EKState>> deltaErrSinks = createDeltaWithErrorSinks(badStates, delta);
		Set<Pair<EKState,EKState>> deltaErrPre = filterDeltaByStates(errStates, deltaErrSinks);
		// no way to add SF yet
		ExtKripke errPre = new ExtKripke();
		errPre.initStates = Utils.intersection(this.initStates, errStates);
		errPre.allStates = errStates;
		errPre.delta = deltaErrPre;
		errPre.deltaActions = this.deltaActions;
		return errPre;
	}

	public ExtKripke createErrPost() {
		ExtKripke errPost = new ExtKripke();
		errPost.initStates = errorBoundary();
		errPost.allStates = this.allStates;
		errPost.delta = this.delta;
		errPost.deltaActions = this.deltaActions;
		return errPost;
	}

	public String getStrNANPS() {
		StringBuilder builder = new StringBuilder();

		builder.append("NANPS\n");
		for (EKState s : this.notAlwaysNotPhiStates()) {
			builder.append("  " + s + "\n");
		}

		return builder.toString();
	}


	public Set<EKState> safetyBoundary() {
		return calculateBoundary(BoundaryType.safety);
	}

	public Set<EKState> robustSafetyBoundary() {
		// the set of states that leave the env, but are guaranteed to be 1-step safe
		final Set<EKState> nonEnvStates = Utils.setMinus(this.allStates, this.envStates);
		return Utils.setMinus(calculateBoundary(BoundaryType.safety, nonEnvStates), calculateBoundary(BoundaryType.safety, this.badStates));
	}

	private Set<EKState> errorBoundary() {
		return calculateBoundary(BoundaryType.error);
	}

	// returns a map of (action name) -> (safety boundary for the action)
	public Map<String, Set<EKState>> safetyBoundaryPerAction() {
		return boundaryPerAction(safetyBoundary());
	}

	// runs under the assumption that: this.envStates \cap this.badStates = \emptyset
	// returns a map of (action name) -> (robust safety boundary for the action)
	public Map<String, Set<EKState>> robustSafetyBoundaryPerAction() {
		// nonEnvStates = goodStates \cap envStates
		// we have by assumption: envStates \subseteq goodStates
		// so: badStates \subseteq nonEnvStates
		final Set<EKState> nonEnvStates = Utils.setMinus(this.allStates, this.envStates);
		final Set<EKState> goodNonEnvStates = Utils.setMinus(nonEnvStates, this.badStates);
		final Set<EKState> envBoundaryStates = calculateBoundary(BoundaryType.safety, goodNonEnvStates);
		Map<String, Set<EKState>> leaveEnv = boundaryPerAction(envBoundaryStates, goodNonEnvStates);

		// so far we have calculated (state,action) pairs such that there EXISTS a world in which the action
		// safely leaves the environment. however, we want (state,action) pairs in which the action ALWAYS
		// safely leaves the environment. we do this by removing any states at the safety boundary for the
		// given action.
		final Map<String, Set<EKState>> safetyBoundary = safetyBoundaryPerAction();
		for (final String act : safetyBoundary.keySet()) {
			if (leaveEnv.containsKey(act)) {
				// remove any states that can lead to an error through this action in 1 step
				final Set<EKState> robustSafetyBoundaryForAct = Utils.setMinus(leaveEnv.get(act), safetyBoundary.get(act));
				if (robustSafetyBoundaryForAct.isEmpty()) {
					leaveEnv.remove(act);
				} else {
					leaveEnv.put(act, robustSafetyBoundaryForAct);
				}
			}
		}
		return leaveEnv;
	}

	// returns a map of (action name) -> (error boundary for the action)
	public Map<String, Set<EKState>> errorBoundaryPerAction() {
		return boundaryPerAction(errorBoundary());
	}


	private Set<EKState> calculateBoundary(BoundaryType boundaryType) {
		return calculateBoundary(boundaryType, this.badStates);
	}

	// invariant: all states in frontier are safe (not in errorStates)
	private Set<EKState> calculateBoundary(final BoundaryType boundaryType, final Set<EKState> errorStates) {
		Set<EKState> goodInitStates = Utils.setMinus(this.initStates, errorStates);
		Set<EKState> explored = new HashSet<>(goodInitStates);
		Set<EKState> frontier = new HashSet<>(goodInitStates);
		Set<EKState> boundary = (boundaryType.equals(BoundaryType.safety)) ?
				new HashSet<>() : Utils.intersection(this.initStates, errorStates);

		while (!frontier.isEmpty()) {
			Set<EKState> addToFrontier = new HashSet<>();
			for (EKState s : frontier) {
				explored.add(s);
				for (EKState t : this.succ(s)) {
					if (errorStates.contains(t)) {
						// the state which we add to the boundary depends on whether we're calculating:
						// the safety boundary or (else) the error boundary
						switch (boundaryType) {
						case safety:
							boundary.add(s);
							break;
						case error:
							boundary.add(t);
							break;
						}
					}
					else if (!explored.contains(t)) {
						addToFrontier.add(t);
					}
				}
			}
			frontier.addAll(addToFrontier);
			frontier.removeAll(explored);
		}
		return boundary;
	}

	private Map<String, Set<EKState>> boundaryPerAction(final Set<EKState> entireBoundary) {
		return boundaryPerAction(entireBoundary, this.badStates);
	}

	private Map<String, Set<EKState>> boundaryPerAction(final Set<EKState> entireBoundary, final Set<EKState> errorStates) {
		Map<String, Set<EKState>> groupedBoundaries = new HashMap<>();
		for (EKState s : entireBoundary) {
			final EKState boundaryState = s;
    		for (EKState t : succ(s)) {
    			Pair<EKState,EKState> transition = new Pair<>(s,t);
    			if (this.delta.contains(transition) && errorStates.contains(t)) {
    				final String act = this.deltaActions.get(transition);
    				if (!groupedBoundaries.containsKey(act)) {
    					groupedBoundaries.put(act, new HashSet<>());
    				}
    				groupedBoundaries.get(act).add(boundaryState);
    			}
    		}
    	}
    	return groupedBoundaries;
    }

	private Set<EKState> succ(EKState s) {
		Set<EKState> succStates = new HashSet<>();
		for (Pair<EKState,EKState> t : this.delta) {
			if (s.equals(t.first)) {
				succStates.add(t.second);
			}
		}
		return succStates;
	}
    
    private Set<String> enabledActions(EKState s) {
    	Set<String> enabled = new HashSet<>();
    	for (Pair<EKState,EKState> t : this.delta) {
    		if (s.equals(t.first)) {
    			final String a = this.deltaActions.get(t);
    			enabled.add(a);
    		}
    	}
    	return enabled;
    }
    
    /**
     * Includes the param names in the action
     * @param s
     * @return
     */
    private Set<Pair<String, EKState>> outgoingTransitions(EKState s) {
    	Set<Pair<String, EKState>> outgoing = new HashSet<>();
    	for (Pair<EKState,EKState> t : this.delta) {
    		if (s.equals(t.first)) {
    			for (final String a : this.deltaActionsWithParams.get(t)) {
        			final Pair<String, EKState> p = new Pair<String, EKState>(a, t.second);
        			outgoing.add(p);
    			}
    		}
    	}
    	return outgoing;
    }

	private Set<EKState> notAlwaysNotPhiStates() {
		Set<EKState> states = new HashSet<>();
		Set<Pair<EKState,EKState>> inverseDelta = invertTransitionRelation(delta);
		for (EKState errState : this.errorBoundary()) {
			// perform a DFS (on inverse delta) from errState. add every state we find to "states"
			// discoverDFS will mutate "states"
			discoverDFS(errState, inverseDelta, states);
		}
		return states;
	}

	private static Set<Pair<EKState,EKState>> filterDeltaByStates(Set<EKState> states, Set<Pair<EKState,EKState>> delta) {
		Set<Pair<EKState,EKState>> deltaFiltered = new HashSet<>();
		for (Pair<EKState,EKState> t : delta) {
			if (states.contains(t.first) && states.contains(t.second)) {
				deltaFiltered.add(t);
			}
		}
		return deltaFiltered;
	}

	private static Set<Pair<EKState,EKState>> createDeltaWithErrorSinks(Set<EKState> errStates, Set<Pair<EKState,EKState>> delta) {
		Set<Pair<EKState,EKState>> deltaWithErrorSinks = new HashSet<>();
		for (Pair<EKState,EKState> t : delta) {
			if (!errStates.contains(t.first)) {
				deltaWithErrorSinks.add(t);
			}
		}
		return deltaWithErrorSinks;
	}

	private static Set<Pair<EKState,EKState>> invertTransitionRelation(Set<Pair<EKState,EKState>> d) {
		Set<Pair<EKState,EKState>> inverse = new HashSet<>();
		for (Pair<EKState,EKState> t : d) {
			inverse.add(new Pair<EKState,EKState>(t.second, t.first));
		}
		return inverse;
	}

	private static void discoverDFS(EKState start, Set<Pair<EKState,EKState>> delta, Set<EKState> states) {
		// base case
		if (states.contains(start)) {
			return;
		}

		states.add(start);
		for (Pair<EKState,EKState> t : delta) {
			if (start.equals(t.first)) {
				discoverDFS(t.second, delta, states);
			}
		}
	}

	// compute the representation for \eta(m2,P) - \eta(m1,P)
	// note: \eta(m2,P) - \eta(m1,P) = beh(m1_err) - beh(m2_err)
	// i.e. we find all erroneous behaviors of m1 that are NOT erroneous behaviors of m2
	public static Set<Pair<EKState,String>> behaviorDifferenceRepresentation(final ExtKripke m1, final ExtKripke m2, final ExtKripke refKripke) {
		final Set<EKState> mutualReach = mutualReach(m1, m2);
		final Set<Pair<EKState,EKState>> m1MinusM2Delta = Utils.setMinus(m1.delta, m2.delta);
		final Set<Pair<EKState,String>> rep = new HashSet<>();
		for (final Pair<EKState,EKState> transition : m1MinusM2Delta) {
			final EKState s = transition.first;
			final EKState t = transition.second;
			if (mutualReach.contains(s) && refKripke.isBadState(t)) {
				// found an outgoing transition (of ONLY m1) from s to a bad state
				final String act = m1.deltaActions.get(transition);
				rep.add(new Pair<EKState,String>(s, act));
			}
		}
    	return rep;
    }
    
    private static Set<EKState> mutualReach(final ExtKripke m1, final ExtKripke m2) {
    	Set<EKState> reach = new HashSet<>();
    	Set<EKState> mutualInit = Utils.intersection(m1.initStates, m2.initStates);
    	Set<Pair<EKState,EKState>> mutualDelta = Utils.intersection(m1.delta, m2.delta);
    	for (EKState init : mutualInit) {
        	mutualReach(mutualDelta, init, reach);
    	}
    	return reach;
    }
    
    private static void mutualReach(final Set<Pair<EKState,EKState>> mutualDelta, final EKState init, Set<EKState> reach) {
    	reach.add(init);
    	for (Pair<EKState,EKState> t : mutualDelta) {
    		if (init.equals(t.first)) {
    			EKState succ = t.second;
    			if (!reach.contains(succ)) {
    				mutualReach(mutualDelta, succ, reach);
    			}
    		}
    	}
    }
    
    
    // print a TLA+ spec
    
    private String toFSPAction(final String s) {
    	return s.toLowerCase();
    }
    
    public String toFSP() {
    	Utils.assertTrue(this.initStates.size() == 1, "We only support 1 init state for right now");
    	
    	StringBuilder builder = new StringBuilder();

    	// assign a name to each state
    	int stateNum = 0;
    	Map<EKState, String> stateNames = new HashMap<>();
    	for (final EKState s : this.allStates) {
    		final int num = stateNum++;
    		final String name = "S" + num;
    		stateNames.put(s, name);
    	}
    	
    	// generate FSP
    	String initStateDef = "";
    	ArrayList<String> nonInitStateDefs = new ArrayList<>();
    	for (final EKState s : this.allStates) {
    		final String name = stateNames.get(s);
    		final Set<Pair<String, EKState>> outgoing = outgoingTransitions(s);
    		final String actions = outgoing
    			.stream()
    			.map(outg -> toFSPAction(outg.first) + " -> " + stateNames.get(outg.second))
    			.collect(Collectors.joining(" | "));
    		final String actionBody = outgoing.isEmpty() ? " = STOP" : " = (" + actions + ")";
    		final String stateDef = name + actionBody;
    		if (this.initStates.contains(s)) {
    			//System.out.println("init state: " + name);
    			initStateDef = stateDef;
    		} else {
        		nonInitStateDefs.add(stateDef);
    		}
    	}
    	final String fsp = initStateDef + ",\n" + String.join(",\n", nonInitStateDefs) + ".";
    	return fsp;
    }
    
    public String toPartialTLASpec(String varsSeqName, String specFairness, boolean strongFairness) {
    	StringBuilder builder = new StringBuilder();
    	
    	//String initOp = "Init_" + tag;
    	//String nextOp = "Next_" + tag;
    	//String specOp = "Spec_" + tag;
    	final String initOp = "Init";
    	final String nextOp = "Next";
    	final String specOp = "Spec";
    	
    	// Init operator
    	builder.append(initOp).append(" ==\n  ").append(initExpr());
    	builder.append("\n\n");
    	
    	// Next operator
    	builder.append(nextOp).append(" ==\n  ").append(nextExpr());
    	builder.append("\n\n");
    	
    	// Spec operator
    	builder.append(specOp).append(" == ")
    		.append(initOp).append(" /\\ [][")
    		.append(nextOp).append("]_").append(varsSeqName);
    	if (!specFairness.isEmpty() && !strongFairness) {
    		builder.append(" /\\ ").append(specFairness);
    	}
    	if (strongFairness) {
    		builder.append(" /\\ SF_").append(varsSeqName).append("(").append(nextOp).append(")");
    	}
    	
    	return builder.toString();
    }

	private String initExpr() {
		if (this.initStates.isEmpty()) {
			return "FALSE";
		}
		return "\\/ " + String.join("\n  \\/ ", statesToStringList(this.initStates));
	}

	private String nextExpr() {
		ArrayList<String> strTransitions = new ArrayList<>();
		for (Pair<EKState,EKState> t : delta) {
			EKState pre = t.first;
			//String post = "(" + format(t.second.toString()) + ")'";
			String post = primeVars(t.second.toString());
			String action = pre + " /\\ " + post;
			strTransitions.add(action);
		}
		if (strTransitions.isEmpty()) {
			return "FALSE";
		}
		return "\\/ " + String.join("\n  \\/ ", strTransitions);
	}

	private static String primeVars(String expr) {
		String[] strs = expr.split("\\s*="); // matches any number of white space characters
		return String.join("' =", strs);
	}

	private static ArrayList<String> statesToStringList(Set<EKState> set) {
		ArrayList<String> arr = new ArrayList<>();
		for (EKState s : set) {
			arr.add(s.toString());
		}
		return arr;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();

		builder.append("Init States\n");
		for (EKState s : initStates) {
			builder.append("  " + s + "\n");
		}

		builder.append("All States\n");
		for (EKState s : allStates) {
			builder.append("  " + s + "\n");
		}

		builder.append("Bad States\n");
		for (EKState s : badStates) {
			builder.append("  " + s + "\n");
		}

		builder.append("Delta\n");
		for (Pair<EKState,EKState> transition : delta) {
			EKState src = transition.first;
			EKState dst = transition.second;
			String act = deltaActions.get(transition);
			Utils.assertNotNull(act, "Found null action!");
			builder.append("  " + act + ": (" + src + ", " + dst + ")\n");
		}

		return builder.toString();
	}
}
