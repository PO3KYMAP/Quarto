package utwente.module2.quarto.gamelogic;

public enum Piece {

    L_S_R_SOLID(Color.LIGHT, Size.SMALL, Shape.ROUND, Fill.SOLID),
    D_S_R_SOLID(Color.DARK, Size.SMALL, Shape.ROUND, Fill.SOLID),
    L_B_R_SOLID(Color.LIGHT, Size.BIG, Shape.ROUND, Fill.SOLID),
    D_B_R_SOLID(Color.DARK, Size.BIG, Shape.ROUND, Fill.SOLID),

    L_S_S_SOLID(Color.LIGHT, Size.SMALL, Shape.SQUARE, Fill.SOLID),
    D_S_S_SOLID(Color.DARK, Size.SMALL, Shape.SQUARE, Fill.SOLID),
    L_B_S_SOLID(Color.LIGHT, Size.BIG, Shape.SQUARE, Fill.SOLID),
    D_B_S_SOLID(Color.DARK, Size.BIG, Shape.SQUARE, Fill.SOLID),

    L_S_R_HOLLOW(Color.LIGHT, Size.SMALL, Shape.ROUND, Fill.HOLLOW),
    D_S_R_HOLLOW(Color.DARK, Size.SMALL, Shape.ROUND, Fill.HOLLOW),
    L_B_R_HOLLOW(Color.LIGHT, Size.BIG, Shape.ROUND, Fill.HOLLOW),
    D_B_R_HOLLOW(Color.DARK, Size.BIG, Shape.ROUND, Fill.HOLLOW),

    L_S_S_HOLLOW(Color.LIGHT, Size.SMALL, Shape.SQUARE, Fill.HOLLOW),
    D_S_S_HOLLOW(Color.DARK, Size.SMALL, Shape.SQUARE, Fill.HOLLOW),
    L_B_S_HOLLOW(Color.LIGHT, Size.BIG, Shape.SQUARE, Fill.HOLLOW),
    D_B_S_HOLLOW(Color.DARK, Size.BIG, Shape.SQUARE, Fill.HOLLOW);

    private final Color color;
    private final Size size;
    private final Shape shape;
    private final Fill fill;

    Piece(Color color, Size size, Shape shape, Fill fill) {
        this.color = color;
        this.size = size;
        this.shape = shape;
        this.fill = fill;
    }

    public Color getColor() { return color; }
    public Size getSize() { return size; }
    public Shape getShape() { return shape; }
    public Fill getFill() { return fill; }

    public int toProtocolId() {
        int id = 0;
        if (color == Color.DARK)   id |= 1;
        if (size == Size.BIG)    id |= 2;
        if (shape == Shape.SQUARE) id |= 4;
        if (fill == Fill.HOLLOW)   id |= 8;
        return id;
    }

    public static Piece fromProtocolId(int id) {
        if (id < 0 || id > 15) {
            throw new IllegalArgumentException("Invalid protocol id: " + id);
        }

        Color color = (id & 1) == 0 ? Color.LIGHT : Color.DARK;
        Size size = (id & 2) == 0 ? Size.SMALL : Size.BIG;
        Shape shape = (id & 4) == 0 ? Shape.ROUND : Shape.SQUARE;
        Fill fill = (id & 8) == 0 ? Fill.SOLID : Fill.HOLLOW;

        for (Piece piece : values()) {
            if (piece.color == color &&
                    piece.size == size &&
                    piece.shape == shape &&
                    piece.fill == fill) {
                return piece;
            }
        }
        throw new IllegalStateException("Piece not found for id " + id);
    }

    @Override
    public String toString() {
        // Color: ☼ = Light, ☾ = Dark
        String c = color == Color.LIGHT ? "☼" : "☾";

        // Size: ↓ = Small, ↑ = Big
        String s = size == Size.SMALL ? "↓" : "↑";

        // Shape + Fill
        String sh;
        if (shape == Shape.ROUND) {
            sh = fill == Fill.SOLID ? "●" : "○"; // solid = ●, hollow = ○
        } else { // Shape.SQUARE
            sh = fill == Fill.SOLID ? "■" : "□"; // solid = ■, hollow = □
        }

        return c + s + sh;
    }

    //Not used
    public String symbol() {
        String s = "";

        // Shape + Fill
        if (getShape() == Shape.ROUND) {
            s = getFill() == Fill.SOLID ? "●" : "○";
        } else { // SQUARE
            s = getFill() == Fill.SOLID ? "■" : "□";
        }

        // Size adjustment
        if (getSize() == Size.BIG) {
            switch (s) {
                case "●": s = "◉"; break;
                case "○": s = "◌"; break;
                case "■": s = "▣"; break;
                case "□": s = "▦"; break;
            }
        }
        return s;
    }
}

//◎●▣■○•□▪
