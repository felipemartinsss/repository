echo -e "Digite o numero de rounds: "
read rounds
./run rddl.competition.Server files/final_comp/rddl 2323 $rounds 123456 rddl.viz.GenericScreenDisplay
