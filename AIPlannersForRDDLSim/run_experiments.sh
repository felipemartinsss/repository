#!/bin/bash
# Script para execução de experimentos no Linux durante o desenvolvimento.
# java "-Xms2512m" "-Xmx2512m" -cp ".:bin:lib/java_cup.jar:lib/grappa1_4.jar:lib/jlex.jar:xercesImpl.jar:xml-apis.jar" "rddl.sim.Simulator" "files/final_comp/rddl" 'rddl.solver.mdp.refactored.sbisimulation.ReachMRFSWithLRTDP' navigation_inst_mdp__10
MIN_RAM="-Xms2512m"
MAX_RAM="-Xmx2512m"
CLASSPATH=".:bin:lib/java_cup.jar:lib/grappa1_4.jar:lib/jlex.jar:xercesImpl.jar:xml-apis.jar"
SIMULATOR="rddl.sim.Simulator"
PROBLEM_FOLDER="files/final_comp/rddl"
DISPLAY_CLASS=""

# ReachMRFS-*, TVI e LRTDP
declare -a ALL_PROBLEMS=(
	"crossing_traffic_inst_mdp__1"
	"crossing_traffic_inst_mdp__2"
	"crossing_traffic_inst_mdp__3"
	"crossing_traffic_inst_mdp__4"
	"elevators_inst_mdp__1"
	"elevators_inst_mdp__2"
	"elevators_inst_mdp__3"
	"elevators_inst_mdp__4"
	"elevators_inst_mdp__7"
	"game_of_life_inst_mdp__1"
	"game_of_life_inst_mdp__2"
	"game_of_life_inst_mdp__3"
	"navigation_inst_mdp__1"
	"navigation_inst_mdp__2"
	"navigation_inst_mdp__3"
	"navigation_inst_mdp__4"
	"navigation_inst_mdp__5"
	"navigation_inst_mdp__6"
	"navigation_inst_mdp__7"
	"navigation_inst_mdp__8"
	"navigation_inst_mdp__9"
	"navigation_inst_mdp__10"
	"skill_teaching_inst_mdp__1"
	"skill_teaching_inst_mdp__2"
	"skill_teaching_inst_mdp__3"
	"skill_teaching_inst_mdp__4"
)

# MRFS-*
declare -a EASY_PROBLEMS=(
	"crossing_traffic_inst_mdp__1"
	"crossing_traffic_inst_mdp__2"
	"elevators_inst_mdp__1"
	"game_of_life_inst_mdp__1"
	"game_of_life_inst_mdp__2"
	"game_of_life_inst_mdp__3"
	"navigation_inst_mdp__1"
	"navigation_inst_mdp__2"
	"skill_teaching_inst_mdp__1"
	"skill_teaching_inst_mdp__2"
	"skill_teaching_inst_mdp__3"
	"skill_teaching_inst_mdp__4"
)

# Enumerative VI
declare -a VERY_EASY_PROBLEMS=(
	"crossing_traffic_inst_mdp__1"
	"crossing_traffic_inst_mdp__2"
	"elevators_inst_mdp__1"
	"elevators_inst_mdp__4"
	"elevators_inst_mdp__7"
	"game_of_life_inst_mdp__1"
	"game_of_life_inst_mdp__2"
	"game_of_life_inst_mdp__3"
	"navigation_inst_mdp__1"
	"navigation_inst_mdp__2"
	"skill_teaching_inst_mdp__1"
	"skill_teaching_inst_mdp__2"
)

declare -a BEST_SOLUTIONS=(
			'rddl.solver.mdp.refactored.sbisimulation.ReachMRFSWithValueIteration'	
			'rddl.solver.mdp.refactored.sbisimulation.ReachMRFSWithTopologicalValueIteration' 				'rddl.solver.mdp.refactored.sbisimulation.ReachMRFSWithLRTDP'
			'rddl.solver.mdp.refactored.planners.off_LRTDPEnum' 				'rddl.solver.mdp.refactored.planners.TVI'  
)

declare -a GOOD_SOLUTIONS=(
			'rddl.solver.mdp.refactored.sbisimulation.MRFSWithValueIteration'	
			'rddl.solver.mdp.refactored.sbisimulation.MRFSWithTopologicalValueIteration' 				'rddl.solver.mdp.refactored.sbisimulation.MRFSWithLRTDP' 
)

declare -a WORSE_SOLUTIONS=(
				'rddl.solver.mdp.refactored.planners.EnumerativeVI'  
)

function experiments {
	echo "Function experiments called..."
	time (java $MIN_RAM $MAX_RAM -cp $CLASSPATH $SIMULATOR $PROBLEM_FOLDER $2 $1) 2>> "experiments/""$2""_""$1"".txt"
}

COUNTER=0
while [ $COUNTER -lt 1 ]; do 
	for s in ${BEST_SOLUTIONS[@]}; do
		for p in ${ALL_PROBLEMS[@]}; do
			experiments $p $s
		done
	done

	for t in ${GOOD_SOLUTIONS[@]}; do
		for q in ${EASY_PROBLEMS[@]}; do
			experiments $q $t
		done
	done

	for u in ${WORSE_SOLUTIONS[@]}; do
		for r in ${VERY_EASY_PROBLEMS[@]}; do
			experiments $r $u
		done
	done

	let COUNTER=COUNTER+1
done

