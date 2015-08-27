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

char *my_strcpy( char *dst, const char *src )
{
	/* implementation intentionally uses pointer arithmetic */
	int c = 1;
	char *d = dst;
    while (c)
    {
    	c = *src;
    	*dst = c;
    	src++;
    	dst++;
    };
    return d;
}