// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import tlc2.Utils;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.impl.Value;
import util.UniqueString;

public final class Action implements ToolGlobals, Serializable {
	private static final UniqueString UNNAMED_ACTION = UniqueString.uniqueStringOf("UnnamedAction");

	public static final Action UNKNOWN = new Action(SemanticNode.nullSN, Context.Empty, UNNAMED_ACTION, false, false);

  /* A TLA+ action.   */

  /* Fields  */
  public final SemanticNode pred;     // Expression of the action
  public final Context con;           // Context of the action
  private final UniqueString actionName;
  private OpDefNode opDef = null;
  private int id;
  private final boolean isInitPred;
  private final boolean isInternal;
  public CostModel cm = CostModel.DO_NOT_RECORD;

  /* Constructors */
  public Action(SemanticNode pred, Context con) {
	  this(pred, con, false);
  }
  
  public Action(SemanticNode pred, Context con, boolean isInitPred) {
	  this(pred, con, UNNAMED_ACTION, isInitPred, false);
  }

  private Action(SemanticNode pred, Context con, UniqueString actionName, boolean isInitPred, final boolean isInternal) {
	  this.pred = pred;
	  this.con = con;
	  this.actionName = actionName;
	  this.isInitPred = isInitPred;
	  this.isInternal = isInternal;
  }

  public Action(SemanticNode pred, Context con, OpDefNode opDef) {
	  this(pred, con, opDef, false, false);
  }

  public Action(SemanticNode pred, Context con, OpDefNode opDef, boolean isInitPred, final boolean isInternal) {
	  this(pred, con, opDef != null ? opDef.getName() : UNNAMED_ACTION, isInitPred, isInternal);
	  // opDef null when action not declared, i.e. Spec == x = 0 /\ ...
	  // See test64 and test64a and others.
	  this.opDef = opDef;
  }
  
  public String actionNameWithoutPrams() {
	  final String rawActName = this.getName().toString();
	  char c[] = rawActName.toCharArray();
	  c[0] = Character.toLowerCase(c[0]);
	  return new String(c);
  }
  
  public String actionNameWithParams() {
	  // add param values to the action
	  final Map<String, Value> mp = this.con.toStrMap();
	  final String actSuffix = Utils.toArrayList(getOpDef().getParams())
			  .stream()
		      .map(p -> p.getSignature()) // the signature is a key for the param value
		      .map(k -> mp.get(k)) // look up the param value from the key
		      .map(v -> v.toString().replace("\"", "")) // turn the value into a string
		      .collect(Collectors.joining("_"));
	  return this.actionNameWithoutPrams() + "_" + actSuffix;
  }

/* Returns a string representation of this action.  */
  public final String toString() {
    return "<Action " + pred.toString() + ">";
  }

  public final String getLocation() {
	  // It is possible that actionName is "Action" but lets ignore it for now.
	  if (isNamed()) {
		  // If known, print the action name instead of the generic string "Action".
	      return getLocation(actionName.toString());
	  }
	  return getLocation("Action");
  }
  
  public final String getLocation(final String actionName) {
      return "<" + actionName + " " +  pred.getLocation() + ">";
  }
  
  public final boolean isNamed() {
	  return actionName != UNNAMED_ACTION && actionName != null && !"".equals(actionName.toString());
  }
  
  /**
   * @return The name of this action. Can be {@link Action#UNNAMED_ACTION}.
   */
  public final UniqueString getName() {
	  return actionName;
  }
  
	public final String getNameOfDefault() {
		if (isNamed()) {
			return getName().toString();
		}
		// If we have an unnamed action, action name will be
		// the string representation of the action (which has information
		// about line, column etc).
		return toString();
	}
  
	/**
	 * @return The OpDefNode corresponding to this Action or <code>null</code> if
	 *         the Action is not explicitly declared. I.e. "Spec == x = 42 /\ [][x'
	 *         = x + 1]_x".
	 */
	public final OpDefNode getOpDef() {
		return this.opDef;
	}

	public final boolean isDeclared() {
		// Spec == x = 0 /\ [][x' = x + 1]_x  has no declared actions.
		return getDeclaration() != Location.nullLoc;
	}
	
	/**
	 * @return The {@link Location} of the <code>Action</code>'s declaration or
	 *         <code>Location.nullLoc</code> if {@link #isDeclared()} is
	 *         false.
	 */
	public Location getDeclaration() {
		if (this.opDef != null) {
			final TreeNode tn = opDef.getTreeNode();
			if (tn != null && tn.one() != null && tn.one().length >= 1) {
				final TreeNode treeNode = tn.one()[0];
				assert treeNode.isKind(SyntaxTreeConstants.N_IdentLHS);
				return treeNode.getLocation();
			}
		}
		return Location.nullLoc;
	}

	public final Location getDefinition() {
	   return pred.getLocation();
	}

	public void setId(int id) {
		this.id = id;
	}
	public int getId() {
		return this.id;
	}
	
	public final boolean isInitPredicate() {
		return isInitPred;
	}

	public boolean isInternal() {
		return isInternal;
	}
	
	@Override
	public int hashCode() {
		return this.getName().hashCode();
	}
	
	@Override
	public boolean equals(Object other) {
		if (other instanceof TLCState) {
			Action o = (Action) other;
			return this.getName().equals(o.getName());
		}
		return false;
	}
}
