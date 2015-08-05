unsigned my_strlen( const char *s )
{
	unsigned i = 0;
	char c = s[i];
	while (c != '\0')
	{
		i++;
		c = s[i];
	}
	return i;
}