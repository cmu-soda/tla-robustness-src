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
import tlc2.tool.EKState;
import tlc2.tool.TLCState;

public class LTSBuilder {
	private Set<EKState> initStates = new HashSet<>();
	private Set<EKState> allStates = new HashSet<>();
	private Set<Triple<EKState,String,EKState>> goodTransitions = new HashSet<>();
	private Set<Pair<EKState,String>> badTransitions = new HashSet<>();
	private Set<String> allActions = new HashSet<>();
	
	
	public int size() {
		return this.allStates.size();
	}
    
    public void addInitState(final TLCState s) {
		final String sName = Utils.normalizeStateString(s.toString());
		final EKState eks = new EKState(sName);
    	this.initStates.add(eks);
    	this.allStates.add(eks);
    }
    
    public void addState(final TLCState s) {
		final String sName = Utils.normalizeStateString(s.toString());
		final EKState eks = new EKState(sName);
    	this.allStates.add(eks);
    }
    
    public void addTransition(final TLCState src, final Action act, final TLCState dst) {
    	final EKState ekSrc = new EKState(Utils.normalizeStateString(src.toString()));
    	final String strAct = act.actionNameWithParams();
    	final EKState ekDst = new EKState(Utils.normalizeStateString(dst.toString()));
    	this.allActions.add(strAct);
    	this.goodTransitions.add(new Triple<>(ekSrc, strAct, ekDst));
    }
    
    public void addTransitionToErr(final TLCState src, final Action act) {
    	final EKState ekSrc = new EKState(Utils.normalizeStateString(src.toString()));
    	final String strAct = act.actionNameWithParams();
    	this.allActions.add(strAct);
    	this.badTransitions.add(new Pair<>(ekSrc, strAct));
    }
    
    public LTS<Integer, String> toNFA() {
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(this.allActions)).create();
    	final Integer ltsErrState = compactNFA.addState(false);
    	
    	Map<EKState, Integer> ekToLtsStates = new HashMap<>();
    	for (final EKState ekState : this.allStates) {
    		final boolean isInitState = this.initStates.contains(ekState);
			final int ltsState = isInitState ? compactNFA.addInitialState(true) : compactNFA.addState(true);
			ekToLtsStates.put(ekState, ltsState);
    	}
    	
    	for (final Triple<EKState,String,EKState> tr : this.goodTransitions) {
    		final Integer src = ekToLtsStates.get(tr.getFirst());
    		final String act = tr.getSecond();
    		final Integer dst = ekToLtsStates.get(tr.getThird());
    		compactNFA.addTransition(src, act, dst);
    	}
    	
    	for (final Pair<EKState,String> tr : this.badTransitions) {
    		final Integer src = ekToLtsStates.get(tr.getFirst());
    		final String act = tr.getSecond();
    		compactNFA.addTransition(src, act, ltsErrState);
    	}
    	
    	return new CompactLTS<String>(compactNFA);
    }
    
    public DetLTS<Integer, String> WA_LTS() {
    	CompactLTS<String> compactLTS = (CompactLTS<String>) toNFA();
    	PerfTimer timer = new PerfTimer();
    	MutableDetLTS<Integer,String> detLTS = LtsUtils.INSTANCE.toDeterministic(compactLTS);
    	System.out.println("Determinize time: " + timer.timeElapsed());
    	return WAHelper.INSTANCE.addTheta(detLTS);
    }
}
