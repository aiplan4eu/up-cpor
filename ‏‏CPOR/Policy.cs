namespace CPOR
{
    abstract class Policy
    {
        public abstract Action GetBestAction(State s);
    }
}
