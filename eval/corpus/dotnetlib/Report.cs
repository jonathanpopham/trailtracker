using System;
using System.IO;

namespace DotNetLib
{
    public interface IReport
    {
        string Render(int score);
    }

    public class Report : IReport
    {
        public string Render(int score) => $"score: {score}";

        public string RenderFile(string path, Scorer scorer, int[] xs)
        {
            var rendered = "";
            try
            {
                var score = scorer.Score(xs);
                rendered = Render(score);
                File.WriteAllText(path, rendered);
            }
            catch (IOException e)
            {
                rendered = e.Message;
            }
            finally
            {
                Cleanup();
            }
            while (rendered.Length > 40)
            {
                rendered = rendered.Substring(0, rendered.Length - 1);
            }
            return rendered;
        }

        private void Cleanup()
        {
            for (int i = 0; i < 3; i++)
            {
                Tick(i);
            }
        }

        private void Tick(int step)
        {
            do
            {
                step--;
            } while (step > 0);
        }
    }
}
