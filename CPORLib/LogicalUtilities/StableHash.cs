namespace CPORLib.LogicalUtilities
{
    internal static class StableHash
    {
        public static int Combine(params string[] parts)
        {
            unchecked
            {
                int hash = 17;
                foreach (string part in parts)
                {
                    hash = hash * 31 + GetStringHash(part);
                }
                return hash;
            }
        }

        public static int GetStringHash(string value)
        {
            unchecked
            {
                int hash = 23;
                string normalized = value ?? string.Empty;
                for (int i = 0; i < normalized.Length; i++)
                {
                    hash = hash * 31 + normalized[i];
                }
                return hash;
            }
        }
    }
}
