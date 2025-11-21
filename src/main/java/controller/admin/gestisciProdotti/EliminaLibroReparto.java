package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import model.libroService.SedeDAO;

import java.io.IOException;

@WebServlet("/eliminaLibro-reparto")
public class EliminaLibroReparto extends HttpServlet {
    private RepartoDAO service;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.service = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String isbn= request.getParameter("isbn");
        int idReparto = Integer.parseInt(request.getParameter("idReparto"));

        if (service == null) {
            service = new RepartoDAO();
        }
        service.deleteFromAppartenenzaLibro(idReparto, isbn);

        RequestDispatcher dispatcher = request.getRequestDispatcher("modifica-libro");
        dispatcher.forward(request, response);
    }
}
