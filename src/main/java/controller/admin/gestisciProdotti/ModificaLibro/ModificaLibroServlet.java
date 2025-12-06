package controller.admin.gestisciProdotti.ModificaLibro;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/modifica-libro")
public class ModificaLibroServlet extends HttpServlet {
    private final ModificaLibroService modificaLibroService = new ModificaLibroService();

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String isbn = request.getParameter("isbn");

        // Liste che passeremo al service per essere riempite
        List<Sede> sedi = new ArrayList<>();
        List<Sede> sediNonPresenti = new ArrayList<>();
        List<Reparto> reparti = new ArrayList<>();
        List<Reparto> repartiNonPresenti = new ArrayList<>();

        // Chiamiamo la logica estratta nel service
        Libro libro = modificaLibroService.preparaDati(
                isbn,
                sedi,
                sediNonPresenti,
                reparti,
                repartiNonPresenti
        );

        // Esattamente gli stessi attribute di prima
        request.setAttribute("libro", libro);
        request.setAttribute("sedi", sedi);
        request.setAttribute("reparti", reparti);
        request.setAttribute("sediNonPresenti", sediNonPresenti);
        request.setAttribute("repartiNonPresenti", repartiNonPresenti);

        RequestDispatcher dispatcher =
                request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/modificaLibro.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/admin/prodotti/modificaLibro.jsp", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/admin/prodotti/modificaLibro.jsp", e);
        }
    }

    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        try {
            doGet(request, response);
        } catch (ServletException | IOException e) {
            log("Errore durante la gestione POST (doGet)", e);
        }
    }
}
