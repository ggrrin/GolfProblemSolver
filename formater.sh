
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
	print $0
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
