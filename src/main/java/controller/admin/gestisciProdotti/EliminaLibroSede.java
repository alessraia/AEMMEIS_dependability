package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.SedeDAO;

import java.io.IOException;
@WebServlet("/eliminaLibro-sede")
public class EliminaLibroSede extends HttpServlet {
    private SedeDAO service;

    public void setSedeDAO(SedeDAO sedeDAO) {
        this.service = sedeDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String isbn= request.getParameter("isbn");
        int idSede = Integer.parseInt(request.getParameter("idSede"));

        if (service == null) {
            service = new SedeDAO();
        }
        service.deleteFromPresenzaLibro(idSede, isbn);

        RequestDispatcher dispatcher = request.getRequestDispatcher("modifica-libro");
        dispatcher.forward(request, response);
    }
}
