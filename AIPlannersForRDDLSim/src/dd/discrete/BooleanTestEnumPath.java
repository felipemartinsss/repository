package dd.discrete;

import java.util.ArrayList;

import util.CString;

public class BooleanTestEnumPath {
	
	// Demonstrates how to enumerate paths in BDDs: the BDDs are created with LOG_AND or LOG_OR.
	public static void main(String[] args) {
			ArrayList<String> vars = new ArrayList();
			vars.add("a");
			vars.add("b");
			vars.add("c");
			ADD context = new ADD(vars);
			int dd = GetLogicalOrDD (context, vars);
			
			// Show the DD whose paths are enumerated
			System.out.println("ADD:\n====\n" + context.printNode(dd));
			
			// Create your leaf processing operation inline as follows
			// Here the path and leaf value are simply printed to System.out
			System.out.println("\nPath enumeration:\n=================");
			context.enumeratePaths(dd, 
				new ADD.ADDLeafOperation() {
					public void processADDLeaf(ArrayList<String> assign,
							double leaf_val) {
						System.out.println(assign + " -> " + leaf_val);
					}
				});
		}

		// Constructs a DD: \and (var ? true(1.0) : false(0.0))
		public static int GetLogicalAndDD (ADD context, ArrayList<String> vars) {
			int ret = context.getBNode (true, true);

			for (String var : vars) {
				Integer high = context.getBNode(true, true);
				Integer low = context.getBNode (false, true);
				int gid = ((Integer) context._hmVarName2ID.get(var)).intValue();
				Integer varNode = context.getINode(gid, low, high, true);
				ret = context.applyInt(ret, varNode, ADD.LOG_AND);
			}
			return ret;
		}
		
		// Constructs a DD: \or (var ? true(1.0) : false(0.0))
		public static int GetLogicalOrDD (ADD context, ArrayList<String> vars) {
			int ret = context.getBNode (false, true);

			for (String var : vars) {
				Integer high = context.getBNode(true, true);
				Integer low = context.getBNode (false, true);
				int gid = ((Integer) context._hmVarName2ID.get(var)).intValue();
				Integer varNode = context.getINode(gid, low, high, true);
				ret = context.applyInt(ret, varNode, ADD.LOG_OR);
			}
			return ret;
		}
		
}
