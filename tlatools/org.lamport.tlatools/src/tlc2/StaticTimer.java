package tlc2;

/**
 * Why use private static variables? Because it's super easy and I'm lazy.
 * @author idardik
 *
 */
public class StaticTimer {
	private static long cummTime = 0L;
	private static long localStartTime = 0L;
	
	public static void enter() {
		StaticTimer.localStartTime = System.currentTimeMillis();
	}
	
	public static void exit() {
		final long latestTimeAddition = System.currentTimeMillis() - StaticTimer.localStartTime;
		StaticTimer.cummTime += latestTimeAddition;
	}
	
	public static long getCummTime() {
		return StaticTimer.cummTime;
	}
}
