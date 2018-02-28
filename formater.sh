
sed -E 's/\[\[/\n\[\[\n/g
s/\]\]/\n\]\]\n/g' $1 | gawk '
/\[\[/{
print $0
RS="],\\[|\\n]"
FS=","
x = 1
}


/\]\]/{
print $0
RS="\n"
FS=","
x = 0
}

{
if( x == 0)
print $0
else
{
	max = 0
	for(i = 1; i <= NF; i++)
	{
		if(match($i, /[0-9]+/))
		{
				max = $i;
				groups[$i] += " "  i " ";
		}
	}
	
	print "max" max

	if( max > 0 )
	{
		for(i = 1; i <= max; i++)
		{
			printf(" | %s", groups[i]);	
		}
		printf("\n");
	}

}
}
k
'
