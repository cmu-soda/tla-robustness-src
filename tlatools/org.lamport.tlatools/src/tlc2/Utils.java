package tlc2;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import tla2sany.semantic.OpDefNode;
import tlc2.tool.Action;
import tlc2.tool.EKState;
import tlc2.tool.TLCState;
import tlc2.value.impl.Value;

public class Utils {
	private static final String QUOTE = "\"";
	private static final String COLON = ":";
	private static final String LSQBRACE = "[";
	private static final String RSQBRACE = "]";
	
	private static final String MAX_NEG_EXAMPLES_ENV_VAR_KEY = "TLA_ROBUST_MAX_NEG_EXAMPLES";
	private static final int DEFAULT_MAX_NEG_EXAMPLES = Integer.MAX_VALUE;
	
	
    public static class Pair<A,B> {
        public A first;
        public B second;
        
        public Pair(A f, B s) {
        	first = f;
        	second = s;
        }
        
        @Override
        public int hashCode() {
        	return first.hashCode() + 5701 * second.hashCode();
        }
        
        @Override
        public boolean equals(Object other) {
        	if (other instanceof Pair<?,?>) {
        		Pair<?,?> p = (Pair<?,?>) other;
        		return this.first.equals(p.first) && this.second.equals(p.second);
        	}
        	return false;
        }
        
        @Override
        public String toString() {
        	return "Pair(" + first.toString() + ", " + second.toString() + ")";
        }
    }
    
    public static <A,B> Set<A> projectFirst(Set<Pair<A,B>> set) {
    	Set<A> proj = new HashSet<A>();
    	for (Pair<A,B> e : set) {
    		proj.add(e.first);
    	}
    	return proj;
    }
    
    
    public static int maxNegExamples() {
    	if (System.getenv().containsKey(MAX_NEG_EXAMPLES_ENV_VAR_KEY)) {
    		final String sval = System.getenv().get(MAX_NEG_EXAMPLES_ENV_VAR_KEY);
    		try {
    			return Integer.parseInt(sval);
    		} catch (NumberFormatException e) {
    			// do nothing, just return the default value
    		}
    	}
    	return DEFAULT_MAX_NEG_EXAMPLES;
    }

	
	/* Because assert() doesn't seem to work */
	
	public static void assertTrue(final boolean condition, final String msg) {
		if (!condition) {
			System.err.println("assertTrue failed with message: " + msg);
			throw new RuntimeException(msg);
		}
	}
	
	public static void assertNull(final Object obj, final String msg) {
		if (obj != null) {
			System.err.println("assertNull failed with message: " + msg);
			throw new RuntimeException("Null assertion failed with message: " + msg);
		}
	}
	
	public static void assertNotNull(final Object obj, final String msg) {
		if (obj == null) {
			System.err.println("assertNotNull failed with message: " + msg);
			throw new RuntimeException("Not-null assertion failed with message: " + msg);
		}
	}
	
	
    public static <T> Set<T> union(Set<T> s1, Set<T> s2) {
    	Set<T> un = new HashSet<T>();
    	un.addAll(s1);
    	un.addAll(s2);
    	return un;
    }
    
    public static <T> Set<T> intersection(Set<T> s1, Set<T> s2) {
    	Set<T> inters = new HashSet<T>();
    	inters.addAll(s1);
    	inters.retainAll(s2);
    	return inters;
    }
    
    public static <T> Set<T> setMinus(Set<T> s1, Set<T> s2) {
    	Set<T> setmin = new HashSet<T>();
    	setmin.addAll(s1);
    	setmin.removeAll(s2);
    	return setmin;
    }
    
    public static <T> T singletonGetElement(Set<T> set) {
    	assert(set.size() == 1);
    	T elem = null;
    	for (T e : set) {
    		elem = e;
    	}
    	return elem;
    }
	
    
    public static ArrayList<Pair<String,String>> extractKeyValuePairsFromState(EKState tlaState) {
    	return extractKeyValuePairsFromState(tlaState.toString());
    }
    
    public static ArrayList<Pair<String,String>> extractKeyValuePairsFromState(String tlaState) {
    	ArrayList<Pair<String,String>> kvPairs = new ArrayList<>();
    	String[] conjuncts = tlaState.split(Pattern.quote("/\\"));
    	for (int i = 0; i < conjuncts.length; ++i) {
    		final String tlaConjunct = conjuncts[i];
    		final Pair<String,String> kvPair = extractKeyValuePairFromAssignment(tlaConjunct);
    		kvPairs.add(kvPair);
    	}
    	return kvPairs;
    }
    
    public static Pair<String, String> extractKeyValuePairFromAssignment(String assg) {
    	String[] kvp = assg.split("=");
		assert(kvp.length == 2);
		final String key = kvp[0].trim();
		final String val = kvp[1].trim();
		if (val.equals("null")) {
			System.err.println("Warning: found null valued state var!");
		}
		return new Pair<>(key,val);
    }
    
    public static String normalizeStateString(String s) {
    	final String[] rawConjuncts = s.replace("\n", "").split(Pattern.quote("/\\"));
    	ArrayList<String> clist = new ArrayList<>();
    	for (int i = 0; i < rawConjuncts.length; ++i) {
    		final String c = rawConjuncts[i].trim();
    		if (!c.isEmpty()) {
    			clist.add(c);
    		}
    	}
    	final String[] conjuncts = toStringArray(clist);
		Arrays.sort(conjuncts);
		return String.join(" /\\ ", conjuncts);
	}
	
	public static String instanceWithList(ArrayList<String> vars) {
    	ArrayList<String> varArrowList = new ArrayList<String>();
    	for (String var : vars) {
    		final String arrow = var + " <- " + var;
    		varArrowList.add(arrow);
    	}
    	return String.join(", ", varArrowList);
    }

    public static <T> ArrayList<T> toArrayList(Set<T> src) {
    	ArrayList<T> dst = new ArrayList<T>();
    	for (T s : src) {
    		dst.add(s);
    	}
    	return dst;
    }

    public static <T> ArrayList<T> toArrayList(T[] src) {
    	ArrayList<T> dst = new ArrayList<T>();
    	for (int i = 0; i < src.length; ++i) {
    		dst.add(src[i]);
    	}
    	return dst;
    }
    
    public static <T> List<String> toStringList(Collection<T> src) {
    	List<String> dst = new ArrayList<>();
    	for (T e : src) {
    		dst.add(e.toString());
    	}
    	return dst;
    }
    
    public static <T> String[] toStringArray(Collection<T> src) {
    	String[] dst = new String[src.size()];
    	int i = 0;
    	for (T e : src) {
    		dst[i++] = e.toString();
    	}
    	return dst;
    }
    
    public static ArrayList<String> filterArrayBlackList(String filter, String[] arr) {
    	ArrayList<String> filtered = new ArrayList<String>();
    	for (int i = 0; i < arr.length; ++i) {
    		String e = arr[i];
    		if (!filter.equals(e)) {
    			filtered.add(e);
    		}
    	}
    	return filtered;
    }
    
    public static ArrayList<String> filterArrayWhiteList(List<String> filter, String[] arr) {
    	ArrayList<String> filtered = new ArrayList<String>();
    	for (int i = 0; i < arr.length; ++i) {
    		String e = arr[i];
    		if (filter.contains(e)) {
    			filtered.add(e);
    		}
    	}
    	return filtered;
    }
    
    public static int findFirstLineOfSpec(ArrayList<String> lines) {
    	for (int i = 0; i < lines.size(); ++i) {
    		String line = lines.get(i);
    		if (line.length() >= 3 && line.substring(0,3).equals("---")) {
    			return i;
    		}
    	}
    	throw new RuntimeException("Unable to find the last line in the TLA+ spec!");
    }
    
    public static int findLastLineOfSpec(ArrayList<String> lines) {
    	for (int i = lines.size()-1; i >= 0; --i) {
    		String line = lines.get(i);
    		if (line.length() >= 3 && line.substring(0,3).equals("===")) {
    			return i;
    		}
    	}
    	throw new RuntimeException("Unable to find the last line in the TLA+ spec!");
    }
    
    public static void printStringArr(ArrayList<String> arr) {
    	for (String s : arr) {
    		System.out.println(s);
    	}
    }
    
    // thanks https://stackoverflow.com/questions/2406121/how-do-i-escape-a-string-in-java
    public static String stringEscape(String s){
	  return s.replace("\\", "\\\\")
	          .replace("\t", "\\t")
	          .replace("\b", "\\b")
	          .replace("\n", "\\n")
	          .replace("\r", "\\r")
	          .replace("\f", "\\f")
	          .replace("\'", "\\'")
	          .replace("\"", "\\\"");
	}
    
    public static String extractSyntaxFromSource(final String tla, final String loc) {
    	String[] parts = loc.replaceAll(",", "").split(" ");
    	int startLine = -1;
    	int startCol = -1;
    	int endLine = -1;
    	int endCol = -1;
    	for (int i = 0; i < parts.length-1; ++i) {
    		final String part = parts[i];
			final String strLineOrColNum = parts[i+1];
    		if (part.equals("line") && startLine < 0) {
    			startLine = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("line") && startLine >= 0) {
    			endLine = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("col") && startCol < 0) {
    			startCol = Integer.parseInt(strLineOrColNum) - 1;
    		}
    		else if (part.equals("col") && startCol >= 0) {
    			endCol = Integer.parseInt(strLineOrColNum);
    		}
    	}
    	assert(startLine >= 0);
    	assert(startCol >= 0);
    	assert(endLine >= 0);
    	assert(endCol >= 0);
    	assert(startLine <= endLine);

    	ArrayList<String> tlaSource = fileContents(tla);
    	// single line extraction
    	if (startLine == endLine) {
    		final String line = tlaSource.get(startLine);
    		final String syntax = line.substring(startCol, endCol);
    		return syntax;
    	}
    	// multi-line extraction
    	else {
        	StringBuilder builder = new StringBuilder();
        	for (int i = startLine; i <= endLine; ++i) {
        		final String line = tlaSource.get(i);
        		if (i == startLine) {
        			builder.append(line.substring(startCol));
        		}
        		else if (i == endLine) {
        			builder.append(" ").append(line.substring(0, endCol));
        		}
        		else {
        			builder.append(" ").append(line);
        		}
        	}
        	return builder.toString();
    	}
    }
    
    public static void writeFile(String file, String contents) {
    	try {
    		BufferedWriter writer = new BufferedWriter(new FileWriter(file));
    	    writer.write(contents);
    	    writer.close();
    	}
    	catch (IOException e) {
    		throw new RuntimeException("Failed to write to file: " + file + "!");
    	}
    }
    
    public static ArrayList<String> fileContents(String loc) {
    	ArrayList<String> lines = new ArrayList<String>();
    	try {
	      Scanner scan = new Scanner(new File(loc));
	      while (scan.hasNextLine()) {
	        lines.add(scan.nextLine());
	      }
	      scan.close();
	    } catch (FileNotFoundException e) {
	      System.out.println("The file " + loc + " does not exist!");
	      e.printStackTrace();
	    }
    	return lines;
    }
	
    public static String asJson(Map<String,String> jsonStrs, Map<String,List<String>> jsonLists) {
    	final String strs = asJsonStrs(jsonStrs);
    	final String lists = asJsonLists(jsonLists);
    	if (strs.isEmpty() && lists.isEmpty()) {
    		return "{}";
    	}
    	else if (strs.isEmpty()) {
        	return "{" + lists + "}";
    	}
    	else if (lists.isEmpty()) {
        	return "{" + strs + "}";
    	}
    	else {
        	return "{" + strs + "," + lists + "}";
    	}
    }
	
    private static String asJsonStrs(Map<String,String> output) {
    	List<String> fields = new ArrayList<>();
    	for (String key : output.keySet()) {
    		final String value = output.get(key);
        	StringBuilder builder = new StringBuilder();
    		builder.append(QUOTE).append(key).append(QUOTE).append(COLON)
    			.append(QUOTE).append(value).append(QUOTE);
    		fields.add(builder.toString());
    	}
    	final String fieldsStr = String.join(",", fields);
    	return fieldsStr;
    }
    
    private static String asJsonLists(Map<String,List<String>> output) {
    	List<String> fields = new ArrayList<>();
    	for (String key : output.keySet()) {
    		final List<String> value = output.get(key);
    		final String flatValue = "\"" + String.join("\",\"", value) + "\"";
        	StringBuilder builder = new StringBuilder();
    		builder.append(QUOTE).append(key).append(QUOTE).append(COLON)
    			.append(LSQBRACE).append(flatValue).append(RSQBRACE);
    		fields.add(builder.toString());
    	}
    	final String fieldsStr = String.join(",", fields);
    	return fieldsStr;
    }
}
