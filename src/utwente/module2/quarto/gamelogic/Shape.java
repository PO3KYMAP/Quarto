package utwente.module2.quarto.gamelogic;

public enum Shape {
    ROUND,
    SQUARE;

    @Override
    public String toString() {
        return switch (this) {
            case ROUND -> "Round";
            case SQUARE -> "Square";
        };
    }
}
