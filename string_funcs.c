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
	char c;
    do
    {
    	c = *src;
    	*dst = c;
    	src++, dst++;
    } while (c != '\0');
    return dst;
}