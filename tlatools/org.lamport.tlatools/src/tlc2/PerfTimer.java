package tlc2;

public class PerfTimer {
	private long startTime;
	
	public PerfTimer() {
		this.startTime = System.currentTimeMillis();
	}
	
	public void reset() {
		this.startTime = System.currentTimeMillis();
	}
	
	public String timeElapsed() {
		final long elapsed = System.currentTimeMillis() - this.startTime;
		return elapsed + "ms";
	}
}
