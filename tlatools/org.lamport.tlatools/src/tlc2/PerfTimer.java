package tlc2;

public class PerfTimer {
	private long startTime;
	
	public PerfTimer() {
		this.startTime = System.currentTimeMillis();
	}
	
	public void reset() {
		this.startTime = System.currentTimeMillis();
	}
	
	public long timeElapsed() {
		return System.currentTimeMillis() - this.startTime;
	}
}
