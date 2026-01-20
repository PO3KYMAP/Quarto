package utwente.module2.quarto.gamelogic;

public enum Size {
    BIG,
    SMALL;

    @Override
    public String toString() {
        return switch (this) {
            case BIG -> "Big";
            case SMALL -> "Small";
        };
    }
}
