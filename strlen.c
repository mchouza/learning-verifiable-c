unsigned my_strlen( const char *s )
{
	unsigned len = 0;
	while (*s != '\0')
	{
		len++;
		s++;
	}
	return len;
}