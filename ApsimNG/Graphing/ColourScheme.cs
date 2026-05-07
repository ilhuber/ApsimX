using System;
using System.Linq;
using System.Drawing;
using System.Collections.Generic;

namespace ApsimNG.Graphing;

internal sealed class ColourScheme
{
    private readonly Color[] colours;
    /// <summary>
    /// The number of colours in this colourscheme.
    /// </summary>
    public int ColourCount => colours.Length;

    public ColourScheme(string[] cols)
    {
        colours = [.. cols.Select(s => ColorTranslator.FromHtml(s))];
    }

    public ColourScheme(Color[] cols)
    {
        colours = cols;
    }

    // TODO: Other constructors that can make gradients and stuff.

    /// <summary>
    /// An enumerable of all the colours.
    /// </summary>
    public IEnumerable<Color> Colours
    {
        get
        {
            foreach (var col in colours)
                yield return col;
        }
    }

    /// <summary>
    /// Gets the nth color. Useful for graphing.
    /// </summary>
    /// <param name="colNum">What color to get. Wraps around.</param>
    /// <returns>The chosen color.</returns>
    public Color ChooseColour(int colNum)
    {
        if (colNum > ColourCount)
            Math.DivRem(colNum, ColourCount, out colNum);
        return colours[colNum];
    }
}