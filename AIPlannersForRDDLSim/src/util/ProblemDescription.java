package util;

import java.math.BigDecimal;
import java.util.HashMap;
import dd.discrete.ADD;
import rddl.solver.mdp.Action;

public class ProblemDescription {
	private int numVars;
	private BigDecimal numStates;
	private long numActions;
	
	public ProblemDescription (ADD _context, HashMap<CString, Action> _hmActionName2Action) {
		numVars = _context._hmID2VarName.size() / 2;
		numStates = new BigDecimal(Math.pow(2, numVars)); 
		numActions = _hmActionName2Action.keySet().size();
	}

	public int getNumVars() {
		return numVars;
	}

	public void setNumVars(int numVars) {
		this.numVars = numVars;
	}

	public BigDecimal getNumStates() {
		return numStates;
	}

	public void setNumStates(BigDecimal numStates) {
		this.numStates = numStates;
	}

	public long getNumActions() {
		return numActions;
	}

	public void setNumActions(long numActions) {
		this.numActions = numActions;
	}
}
