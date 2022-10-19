using CPORLib;




public class Program
{
    private static void Main(string[] args)
    {
        Run.RunPlanner(@"..\..\..\..\Tests\doors5\d.pddl"
            , @"..\..\..\..\Tests\doors5\p.pddl",
            false);
    }
}