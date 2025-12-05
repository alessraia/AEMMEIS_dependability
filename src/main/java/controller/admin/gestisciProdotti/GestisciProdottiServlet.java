package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet("/gestisci-prodotti")
public class GestisciProdottiServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        LibroDAO service = new LibroDAO();
        List<Libro> libri = new ArrayList<Libro>();
        libri= service.doRetriveAll();
        request.setAttribute("libri", libri);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/prodotti/gestisciProdotti.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/admin/prodotti/gestisciProdotti.jsp", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/admin/prodotti/gestisciProdotti.jsp", e);
        }
    }

    public void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
