package util;

import java.util.ArrayList;

import rddl.solver.mdp.Action;

/**
 * Class that represents an action transition.
 * Given a state, we can instantiate one object of this 
 * classe to find which are the reachable states.
 * @author felipemartinsss
 *
 */
public class ActionTransition {
	private Action a;
	private ArrayList <ProbState> actionTransitions;
	private double reward;
	private double qValue;
	
	public ActionTransition (Action a, ArrayList <ProbState> actionTransitions) {
		this.a = a;
		this.actionTransitions = actionTransitions;
	}
	
	public Action getAction() {
		return a;
	}
	
	public ArrayList <ProbState> getTransitions() {
		return actionTransitions;
	}
	
	public void setTransitions (ArrayList <ProbState> transitions) {
		this.actionTransitions = transitions;
	}
	
	public void setReward (double reward) {
		this.reward = reward;
	}
	
	public double getReward () {
		return reward;
	}
	
	public double getQValue() {
		return qValue;
	}
	
	public void setQValue (double qValue) {
		this.qValue = qValue;
	}
	
}
