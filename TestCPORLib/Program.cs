using CPORLib;




public class Program
{
    private static void Main(string[] args)
    {
        Run.RunPlanner(@"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\AIPlan4EU\up-cpor\Tests\doors5\d.pddl"
            , @"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\AIPlan4EU\up-cpor\Tests\doors5\p.pddl",
            false);
    }
}