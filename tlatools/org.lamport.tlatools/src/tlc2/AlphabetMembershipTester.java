package tlc2;

import java.util.Set;

import cmu.isr.ts.LTS;

public class AlphabetMembershipTester {
	private Set<String> actionPrefixes;
	private LTS<Integer,String> lts;
	
	public AlphabetMembershipTester(Set<String> ap, LTS<Integer,String> l) {
		this.actionPrefixes = ap;
		this.lts = l;
	}
	
	public void update(Set<String> ap, LTS<Integer,String> l) {
		this.actionPrefixes.addAll(ap);
		this.lts = l;
	}
	
	/**
	 * If an action <act> is not the alphabet of <lts> then it may still technically be in its
	 * alphabet. It's technically in the alphabet of <lts> when its prefix matches a prefix in
	 * <actionPrefixes>. In this case, <lts> suppresses <act>.
	 * @param pref
	 * @param act
	 * @return
	 */
	public boolean actionIsSuppressed(final String pref, final String act) {
		return actionPrefixes.contains(pref) && !lts.getInputAlphabet().contains(act);
	}
}
