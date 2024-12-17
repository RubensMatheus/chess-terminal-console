package br.com.chess.game.pieces;

import br.com.chess.game.boardgame.Board;
import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.boardgame.Position;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.utils.Color;

public class King extends ChessPiece {
    private ChessMatch chessMatch; //@ in modelMatch;

    //@ public represents maxMove = 2;

    //@ public model ChessMatch modelMatch;
    //@ private represents modelMatch = this.chessMatch;

    /*@ public normal_behavior
      @     ensures modelMatch == chessMatch;
      @     ensures modelBoard == board;
      @     ensures modelColor == color;
      @ pure
      @*/
    public King(Board board, Color color, ChessMatch chessMatch) {
        super(board, color);
        this.chessMatch = chessMatch;
    }

    /*@ also
      @ public normal_behavior
      @     ensures \result.equals("R");
      @ pure
      @*/
    @Override
    public String getString() {
        return "R";
    }

    /*@ requires getBoard().positionExists(position);
      @ ensures \result == (getBoard().pieces[position.getRow()][position.getColumn()] == null ||
      @     (getBoard().pieces[position.getRow()][position.getColumn()] instanceof ChessPiece &&
      @     (getBoard().pieces[position.getRow()][position.getColumn()]).getColor() != this.getColor()));
      @ pure helper
      @*/
    private boolean canMove(Position position) {
        /*@ nullable */ ChessPiece p = getBoard().piece(position);
        if (p == null) {
            return true;
        }
        return p.getColor() != getColor();
    }

    /*@ requires getBoard().positionExists(position);
      @ ensures \result == (getBoard().pieces[position.getRow()][position.getColumn()] != null &&
           getBoard().pieces[position.getRow()][position.getColumn()] instanceof Rook &&
           getBoard().pieces[position.getRow()][position.getColumn()].getColor() == this.getColor() &&
           getBoard().pieces[position.getRow()][position.getColumn()].getMoveCount() == 0);
      @ pure helper
      @*/
    private boolean testRookCastling(Position position) {
        /*@ nullable */ ChessPiece p = getBoard().piece(position);
        if (p == null) {
            return false;
        }
        return p instanceof Rook && p.getColor() == getColor() && p.getMoveCount() == 0;
    }

    @Override
    public boolean[][] possibleMoves() {
        boolean[][] mat = new boolean[getBoard().getRows()][getBoard().getColumns()];

        // Validações iniciais
        if (position == null || !getBoard().positionExists(position)) {
            return mat;
        }

        int[][] directions = {
                {-1, 0},  // acima
                {1, 0},   // abaixo
                {0, -1},  // esquerda
                {0, 1},   // direita
                {-1, -1}, // diagonal superior esquerda
                {-1, 1},  // diagonal superior direita
                {1, -1},  // diagonal inferior esquerda
                {1, 1}    // diagonal inferior direita
        };

        Position p = new Position(0, 0);

        /*@ maintaining 0 <= i && i <= directions.length;
          @ maintaining mat.length == getBoard().getRows();
          @ maintaining mat[0].length == getBoard().getColumns();
          @ maintaining (\forall int x, y;
          @     0 <= x && x < mat.length && 0 <= y && y < mat[x].length;
          @     mat[x][y] ==> (
          @         getBoard().positionExistsBasic(x, y) &&
          @         (getBoard().pieces[x][y] == null ||
          @         (getBoard().pieces[x][y] instanceof ChessPiece &&
          @          getBoard().pieces[x][y].getColor() != this.getColor()))));
          @ decreases directions.length - i;
          @*/
        for (int i = 0; i < directions.length; i++) {
            int[] dir = directions[i];
            p.setValues(position.getRow() + dir[0], position.getColumn() + dir[1]);
            if (getBoard().positionExists(p) && canMove(p)) {
                mat[p.getRow()][p.getColumn()] = true;
            }
        }

        // Movimentos especiais: Roque
        if (getMoveCount() == 0 && !chessMatch.isCheck()) {
            // Roque pequeno (kingside)
            Position kingsideRook = new Position(position.getRow(), position.getColumn() + 3);
            if (getBoard().positionExists(kingsideRook) && testRookCastling(kingsideRook)) {
                Position p1 = new Position(position.getRow(), position.getColumn() + 1);
                Position p2 = new Position(position.getRow(), position.getColumn() + 2);
                if (getBoard().piece(p1) == null && getBoard().piece(p2) == null) {
                    mat[position.getRow()][position.getColumn() + 2] = true;
                }
            }

            // Roque grande (queenside)
            Position queensideRook = new Position(position.getRow(), position.getColumn() - 4);
            if (getBoard().positionExists(queensideRook) && testRookCastling(queensideRook)) {
                Position p1 = new Position(position.getRow(), position.getColumn() - 1);
                Position p2 = new Position(position.getRow(), position.getColumn() - 2);
                Position p3 = new Position(position.getRow(), position.getColumn() - 3);
                if (getBoard().piece(p1) == null && getBoard().piece(p2) == null && getBoard().piece(p3) == null) {
                    mat[position.getRow()][position.getColumn() - 2] = true;
                }
            }
        }

        return mat;
    }
}
