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
	unsigned i = 0;
	char c = src[i];
	while (c != '\0')
	{
		dst[i] = c;
		i++;
		c = src[i];
	}
	return dst;
}