package recomp;

import java.util.HashMap;
import java.util.Map;

import cmu.isr.ts.DetLTS;
import cmu.isr.ts.LTS;
import cmu.isr.ts.lts.CompactLTS;
import cmu.isr.ts.lts.ltsa.LTSACall;
import cmu.isr.ts.lts.ltsa.StringLTSInput;
import cmu.isr.ts.lts.ltsa.StringLTSOutput;
import lts.CompositeState;
import lts.LTSCompiler;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.automata.graphs.TransitionEdge.Property;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.util.minimizer.Block;
import net.automatalib.util.minimizer.MinimizationResult;
import net.automatalib.util.minimizer.Minimizer;
import net.automatalib.words.impl.Alphabets;

public class AutomataLibUtils {
	
	public static LTS<Integer, String> minimizeLTS(LTS<Integer, String> orig) {
    	MinimizationResult<Integer, Property<String, Void>> minResult = Minimizer.minimize( orig.transitionGraphView(orig.getInputAlphabet()) );
    	
    	CompactNFA<String> compactNFA = AutomatonBuilders.newNFA(Alphabets.fromCollection(orig.getInputAlphabet())).create();
    	
    	Map<Integer, Integer> blockToNFAState = new HashMap<>();
    	for (Block<Integer, Property<String, Void>> block : minResult.getBlocks()) {
    		final boolean isInitState = MinimizationResult.getStatesInBlock(block)
    				.stream()
    				.anyMatch(s -> orig.getInitialStates().contains(s));
    		final boolean isAccepting = MinimizationResult.getStatesInBlock(block)
    				.stream()
    				.allMatch(s -> orig.isAccepting(s));
    		final int nfaState = isInitState ? compactNFA.addInitialState(isAccepting) : compactNFA.addState(isAccepting);
    		blockToNFAState.put(block.getId(), nfaState);
    	}
    	
    	for (Block<Integer, Property<String, Void>> srcBlock : minResult.getBlocks()) {
    		final Integer srcNFAState = blockToNFAState.get(srcBlock.getId());
    		final Integer srcOrig = minResult.getRepresentative(srcBlock);
    		for (final String act : orig.getInputAlphabet()) {
    			for (final Integer succOrig : orig.getSuccessors(srcOrig, act)) {
    				final Block<Integer, Property<String, Void>> succBlock = minResult.getBlockForState(succOrig);
    	    		final Integer succNFAState = blockToNFAState.get(succBlock.getId());
    	    		compactNFA.addTransition(srcNFAState, act, succNFAState);
    			}
    		}
    	}
    	
    	return new CompactLTS<>(compactNFA);
	}

	public static DetLTS<Integer, String> fspToDFA(final String fsp) {
    	StringLTSOutput ltsOutput = new StringLTSOutput();
    	LTSCompiler ltsCompiler = new LTSCompiler(new StringLTSInput(fsp), ltsOutput, System.getProperty("user.dir"));
    	CompositeState lts = ltsCompiler.compile("DEFAULT");
    	lts.compose(ltsOutput);
    	return LTSACall.INSTANCE.toDetLTS(lts, false);
    }
    
	public static LTS<Integer, String> fspToNFA(final String fsp) {
    	StringLTSOutput ltsOutput = new StringLTSOutput();
    	LTSCompiler ltsCompiler = new LTSCompiler(new StringLTSInput(fsp), ltsOutput, System.getProperty("user.dir"));
    	CompositeState lts = ltsCompiler.compile("DEFAULT");
    	lts.compose(ltsOutput);
    	return LTSACall.INSTANCE.toLTS(lts, false);
    }
}
