using System.Drawing;
using System.Collections.Generic;
using APSIM.Shared.Utilities;

namespace ApsimNG.Graphing;

static class ColourSchemes
{
    private static readonly ColourScheme defaultColorScheme = new(ColourUtilities.Colours);
    // TODO: Allow users to create a custom colourscheme??
    private static readonly Dictionary<string, ColourScheme> _colorSchemes = new()
    {
        ["Default"] = defaultColorScheme,
        ["APSIM Classic"] = new([Color.Blue, Color.Red, Color.Green,
                                 Color.Orange, Color.Magenta, Color.Cyan,
                                 Color.Brown, Color.Purple, Color.Gray,
                                 Color.DarkBlue, Color.DarkRed, Color.DarkGreen,
                                 Color.DarkOrange, Color.DarkMagenta, Color.DarkCyan,
                                 Color.Firebrick, Color.DarkSalmon, Color.DarkGray]),
        ["Brewer Dark2"] = new(["#1b9e77","#d95f02","#7570b3","#e7298a",
                                "#66a61e","#e6ab02","#a6761d","#666666"]),
        ["ggplot2"] = new(["#F8766D", "#CD9600", "#7CAE00", "#00BE67",
                           "#00BFC4", "#00A9FF", "#C77CFF", "#FF61CC"])
    };

    public static IEnumerable<string> Options => _colorSchemes.Keys;

    public static ColourScheme GetColourScheme(string name)
    {
        if (_colorSchemes.TryGetValue(name, out var ret))
            return ret;
        return defaultColorScheme;
    }
}