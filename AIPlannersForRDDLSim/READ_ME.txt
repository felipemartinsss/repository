RDDLSim is a software developed by Scott Sanner (ssanner@gmail.com) and
Sungwook Yoon (sungwook.yoon@gmail.com).It is a simulator used by 
competitors in the  International Probabilistic Planning Competition 
(IPPC).

RDDLSim url: https://code.google.com/p/rddlsim/

RDDLSim was used by me (felipemartinsss@gmail.com) to develop 
my master degree dissertation and some papers with Leliane Barros, 
Mijail Holguin and Felipe Trevizan. My classes 
are in the following packages: 
- rddl.solver.mdp.rtdp;
- rddl.solver.mdp.sbisimulation; and
- rddl.solver.mdp.vi.

I am making an effort to make my classes more readable with the 
packages:
- rddl.solved.mdp.refactored.planners;
- rddl.solved.mdp.refactored.sbisimulation; and
- util.

*****************************************************************
		Additional information
*****************************************************************

The classes used to compute the paper' results are:
rddl.solver.mdp.rtdp.off_LRTDPEnum
rddl.solver.mdp.vi.EnumerativeVI
rddl.solver.mdp.vi.TVI_FTVI
rddl.solver.mdp.sbisimulation.MRFSWithLRTDP
rddl.solver.mdp.sbisimulation.MRFSWithTopologicalValueIteration
rddl.solver.mdp.sbisimulation.MRFSWithValueIteration
rddl.solver.mdp.sbisimulation.ReachMRFSWithLRTDP
rddl.solver.mdp.sbisimulation.ReachMRFSWithTopologicalValueIteration
rddl.solver.mdp.sbisimulation.ReachMRFSWithValueIteration

****************************************************************
		Running the classes
****************************************************************

To learn how to run the planners, look in the simulator README
(txt/INSTALL.txt) for a section called 'Simulator examples'.