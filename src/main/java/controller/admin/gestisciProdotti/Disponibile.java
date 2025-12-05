package controller.admin.gestisciProdotti;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.RepartoDAO;
import model.libroService.SedeDAO;

import java.io.IOException;

@WebServlet("/disponibile")
public class Disponibile extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String isbn= request.getParameter("isbn");

        LibroDAO service = new LibroDAO();
        Libro libro = service.doRetrieveById(isbn);
        libro.setDisponibile(true);

        service.updateDisponibile(libro);

        RequestDispatcher dispatcher = request.getRequestDispatcher("gestisci-prodotti");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso gestisci-prodotti", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso gestisci-prodotti", e);
        }
    }
}
