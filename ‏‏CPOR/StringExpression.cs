namespace CPOR
{
    class StringExpression : Expression
    {
        public string Value { get; private set; }
        public StringExpression(string sValue)
        {
            Value = sValue;
        }
        public override string ToString()
        {
            return Value;
        }
    }
}
