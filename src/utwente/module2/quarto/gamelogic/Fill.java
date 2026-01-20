package utwente.module2.quarto.gamelogic;

public enum Fill {
    SOLID,
    HOLLOW;

    @Override
    public String toString() {
        return switch (this) {
            case SOLID -> "Solid";
            case HOLLOW -> "Hollow";
        };
    }
}
