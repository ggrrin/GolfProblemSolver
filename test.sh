#!/bin/bash

solver_alias=$1
N=${2:-4}
K=${3:-2}
G=${4:-2}
D=${5:-2}
Opt=${6:-[]}
Variants=${7:-10}



case $solver_alias in
basic) solver=golf_all ;;
day_symetries) solver=golf ;;
*)
echo "test.sh <solver-variant> [N K G D <labeling-opts-params> <variants-count-to-search>]"
echo "<solver-variant> := basic|day_symetries"
exit 1
;;

esac

if ! mkdir -p logs ; then
	echo "Failed to create logs directory!"
	exit 1
fi
log_file="logs/log-$solver_alias-$N-$K-$G-$D-$Opt-$Variants.txt"


ulimit -t 72000 #20 h
echo -n "" > "$log_file"


function set_print_options(){
	echo "set_prolog_flag(debugger_print_options, [max_depth(0)])."
	echo "set_prolog_flag(toplevel_print_options, [max_depth(0)])."
}

function get_alternatives(){
	for (( i = 0; i<$1; i++))
	do
		echo ";"
	done
}

function input(){
	set_print_options
	echo "$solver(T,X,$N,$K,$G,$D, $Opt)."
	get_alternatives $Variants 
	echo 
}


function format-output(){
gawk '
BEGIN{
	 for ( i = 0 ; ++i < 256 ; ) 
	{
		C[i] =  sprintf ( "%c" , i ) 
		if(C[i] == "A")
			A = i; 
	}
}
{
	print $0
}

/^X/{
	match($0, /\[\[(.*)]]/, matrix);
	split(matrix[1], rows, /],\[/);
	for(i = 1; i <= length(rows); i++)
	{	
		maxgroup[i] = 1;
		print rows[i]
		split(rows[i], elements, /,/);
		for(j = 1; j <= length(elements); j++)
		{
			if(maxgroup[i] < elements[j])
				maxgroup[i] = elements[j];

			groups[i,elements[j]] = groups[i,elements[j]] C[A + (j-1)]
		}
	}

	for(i = 1; i <= length(rows); i++)
	{ 
		
		for(g = 1; g <= maxgroup[i]; g++)
		{
			printf("%s | ", groups[i,g]);
			groups[i,g] = ""
		}
		printf("\n");
	}
}
	
' $1
}

input | sicstus -l golf-problem-solver.pl 2>&1 | format-output | tee "$log_file"
exit 0
