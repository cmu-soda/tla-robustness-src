package tlc2;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import cmu.isr.assumption.WAHelper;
import cmu.isr.tolerance.utils.LtsUtils;
import cmu.isr.ts.DetLTS;
import cmu.isr.ts.LTS;
import cmu.isr.ts.MutableDetLTS;
import cmu.isr.ts.lts.CompactLTS;
import kotlin.Pair;
import kotlin.Triple;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.words.impl.Alphabets;
import tlc2.tool.Action;
import tlc2.tool.TLCState;

// TODO addBadInitState() is not properly implemented!!
public class LTSBuilder {
	private Set<LTSBState> initStates = new HashSet<>();
	private Set<LTSBState> allStates = new HashSet<>();
	private Set<Triple<LTSBState,String,LTSBState>> goodTransitions = new HashSet<>();
	private Set<Pair<LTSBState,String>> badTransitions = new HashSet<>();
	private Set<String> allActions = new HashSet<>();


	public int size() {
		return this.allStates.size();
	}

    public void addInitState(final TLCState s) {
		final LTSBState lbs = new LTSBState(s);
    	this.initStates.add(lbs);
    	this.allStates.add(lbs);
    }

    public void addBadInitState(final TLCState s) {
    	// TODO actually do something about this state being bad
    	Utils.assertTrue(false, "addBadInitState isn't implemented!");
		final LTSBState lbs = new LTSBState(s);
    	this.initStates.add(lbs);
    	this.allStates.add(lbs);
    }

    public void addState(final TLCState s) {
		final LTSBState lbs = new LTSBState(s);
    	this.allStates.add(lbs);
    }

    public void addTransition(final TLCState src, final Action act, final TLCState dst) {
    	final LTSBState lbsSrc = new LTSBState(src);
    	final String strAct = act.actionNameWithParams();
    	final LTSBState lbsDst = new LTSBState(dst);
    	this.allActions.add(strAct);
    	this.goodTransitions.add(new Triple<>(lbsSrc, strAct, lbsDst));
    }

    public void addTransitionToErr(final TLCState src, final Action act) {
    	final LTSBState lbsSrc = new LTSBState(src);
    	final String strAct = act.actionNameWithParams();
    	this.allActions.add(strAct);
    	this.badTransitions.add(new Pair<>(lbsSrc, strAct));
    }

    public LTS<Integer, String> toNFAIncludingAnErrorState() {
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(this.allActions)).create();
    	final Integer ltsErrState = compactNFA.addState(false);

    	Map<LTSBState, Integer> lbsToLtsStates = new HashMap<>();
    	for (final LTSBState lbsState : this.allStates) {
    		final boolean isInitState = this.initStates.contains(lbsState);
			final int ltsState = isInitState ? compactNFA.addInitialState(true) : compactNFA.addState(true);
			lbsToLtsStates.put(lbsState, ltsState);
    	}

    	for (final Triple<LTSBState,String,LTSBState> tr : this.goodTransitions) {
    		final Integer src = lbsToLtsStates.get(tr.getFirst());
    		final String act = tr.getSecond();
    		final Integer dst = lbsToLtsStates.get(tr.getThird());
    		compactNFA.addTransition(src, act, dst);
    	}

    	for (final Pair<LTSBState,String> tr : this.badTransitions) {
    		final Integer src = lbsToLtsStates.get(tr.getFirst());
    		final String act = tr.getSecond();
    		compactNFA.addTransition(src, act, ltsErrState);
    	}

    	return new CompactLTS<String>(compactNFA);
    }

    public LTS<Integer, String> toNFAWithoutAnErrorState() {
    	Utils.assertTrue(this.badTransitions.size() == 0, "Called toNFAWithoutAnErrorState() on an unsafe LTS!");
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(this.allActions)).create();

    	Map<LTSBState, Integer> lbsToLtsStates = new HashMap<>();
    	for (final LTSBState lbsState : this.allStates) {
    		final boolean isInitState = this.initStates.contains(lbsState);
			final int ltsState = isInitState ? compactNFA.addInitialState(true) : compactNFA.addState(true);
			lbsToLtsStates.put(lbsState, ltsState);
    	}

    	for (final Triple<LTSBState,String,LTSBState> tr : this.goodTransitions) {
    		final Integer src = lbsToLtsStates.get(tr.getFirst());
    		final String act = tr.getSecond();
    		final Integer dst = lbsToLtsStates.get(tr.getThird());
    		compactNFA.addTransition(src, act, dst);
    	}

    	return new CompactLTS<String>(compactNFA);
    }
    
    
    private static class LTSBState {
    	private final long sid;
    	
    	public LTSBState(final TLCState s) {
    		sid = s.fingerPrint();
    	}
    	
    	@Override
    	public boolean equals(Object o) {
    		if (o instanceof LTSBState) {
    			final LTSBState other = (LTSBState) o;
    			return this.sid == other.sid;
    		}
    		return false;
    	}
    	
    	@Override
    	public int hashCode() {
    		return Long.hashCode(this.sid);
    	}
    }
}