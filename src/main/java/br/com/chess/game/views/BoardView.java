package br.com.chess.game.views;


import br.com.chess.game.boardgame.ChessPiece;
import br.com.chess.game.chess.ChessMatch;
import br.com.chess.game.chess.ChessPosition;
import br.com.chess.game.chess.utils.Color;

import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

public class BoardView {

    //@ assignable System.out.outputText, System.out.eol;
    public static void clearScreen(){
        System.out.print("\033[H\033[2J");
        System.out.flush();
    }

    /*@ assignable \nothing;
      @*/
    public static ChessPosition readChessPosition(Scanner sc) throws InputMismatchException {
        try {
            String s = sc.nextLine();
            char column = s.charAt(0);
            int row = Integer.parseInt(s.substring(1));
            return new ChessPosition(column, row);
        }catch (RuntimeException e){
            throw new InputMismatchException("Erro ao ler a posição no tabuleiro. Valores validos entre a1 até h8");
        }
    }

    //@ assignable System.out.outputText, System.out.eol;
    public static void printMatch(ChessMatch chessMatch, List<ChessPiece> capturedPieces){
        printBoard(chessMatch.getChessPieces());
        System.out.println();
        capturedPieces(capturedPieces);
        System.out.println("Turno: "+ chessMatch.getTurn());
        if (!chessMatch.isCheckMate()){
            System.out.println("Esperando o joagador: "+ chessMatch.getCurrentPlayer());
            if (chessMatch.isCheck()){
                System.out.println("Check!");
            }
        }else {
            System.out.println("CHECKMATE!");
            System.out.println("Vencedor: "+ chessMatch.getCurrentPlayer());
        }

    }


    /*@ requires pieces.length == 8;
      @ assignable System.out.outputText, System.out.eol;
      @*/
    public static void printBoard(ChessPiece[][] pieces) {
        /*@ maintaining 0 <= i && i <= pieces.length;
          @ decreasing pieces.length - i;
          @*/
        for (int i = 0; i < pieces.length; i++) {
            System.out.print((8 - i) + " ");
            /*@ maintaining 0 <= j && j <= pieces[i].length;
              @ decreasing pieces[i].length - j;
              @*/
            for (int j = 0; j < pieces[i].length; j++) {
                printPiece(pieces[i][j], false);
            }
            System.out.println();
        }
        System.out.println("  a b c d e f g h");
    }


    /*@ requires pieces.length == 8;
      @ requires possibleMoves.length == 8;
      @ requires (\forall int x; 0 <= x && x < pieces.length; pieces[x].length == 8);
      @ requires (\forall int x; 0 <= x && x < possibleMoves.length; possibleMoves[x].length == 8);
      @ assignable System.out.outputText, System.out.eol;
      @*/
    public static void printBoard(/*@ nullable*/ ChessPiece[][] pieces, boolean[][] possibleMoves) {
        /*@ maintaining 0 <= i && i <= pieces.length;
          @ decreasing pieces.length - i;
          @*/
        for (int i = 0; i < pieces.length; i++) {
            System.out.print((8 - i) + " ");
            /*@ maintaining 0 <= j && j <= pieces[i].length;
              @ decreasing pieces[i].length - j;
              @*/
            for (int j = 0; j < pieces[i].length; j++) {
                printPiece(pieces[i][j], possibleMoves[i][j]);
            }
            System.out.println();
        }
        System.out.println("  a b c d e f g h");
    }



    /*@ assignable System.out.outputText, System.out.eol;
      @*/
    private static void printPiece(/*@ nullable*/ ChessPiece piece, boolean background) {

        if (background) {
            System.out.print("\u001B[44m");
        }
        if (piece == null) {
            System.out.print("-" + "\u001B[0m");
        } else {
            if (piece.getColor() == Color.WHITE) {
                System.out.print("\u001B[37m" + piece.getString() + "\u001B[0m");
            }
            else {
                System.out.print("\u001B[33m" + piece.getString() + "\u001B[0m");
            }
        }
        System.out.print(" ");
    }

    /*@ assignable System.out.outputText, System.out.eol;
      @*/
    private static void capturedPieces(List<ChessPiece> chessPieces) {
            List<ChessPiece> white = new ArrayList<>();
            List<ChessPiece> black = new ArrayList<>();

            // Filtrar as peças em listas separadas
            for (ChessPiece piece : chessPieces) {
                if (piece.getColor() == Color.WHITE) {
                    white.add(piece);
                } else if (piece.getColor() == Color.BLACK) {
                    black.add(piece);
                }
            }

            System.out.println("Peças capturadas: ");

            // Peças Brancas
            System.out.print("Peças brancas: ");
            System.out.print("\u001B[37m");
            for (int i = 0; i < white.size(); i++) {
                System.out.print(white.get(i).getString());
                if (i < white.size() - 1) {
                    System.out.print(", ");
                }
            }
            System.out.println("\u001B[0m");

            // Peças Pretas
            System.out.print("Peças pretas: ");
            System.out.print("\u001B[33m");
            for (int i = 0; i < black.size(); i++) {
                System.out.print(black.get(i).getString());
                if (i < black.size() - 1) {
                    System.out.print(", ");
                }
            }
            System.out.println("\u001B[0m");
        }

}


